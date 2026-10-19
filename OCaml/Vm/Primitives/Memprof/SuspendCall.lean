import OCaml.Vm.Primitives.Memprof.SetSuspended
import OCaml.Vm.Primitives.Memprof.RenewCall

/-!
# `caml_memprof_set_suspended(1)`

`local->suspended = 1`, then `caml_memprof_renew_minor_sample()`
(`renew_summary`, sampling off), and with `s != 0` the function returns.
The memory facts the renewal reads are stated on the memory after the four
stores of the prologue (`suspendLog`); the reloads after the call are apart
from the renewal's stores.
-/

namespace OCaml.Vm.Primitives.Memprof.SetSuspended
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gprReg_ne_htif gpr_some gpr_some_of)
open OCaml.Vm.Primitives.Memprof.RenewMinorSample (renewLog renew_summary triggerAddr)
open OCaml.Vm.Primitives.Memprof.UpdateYoungLimit (limitValue)

/-- The prologue's stores: `s0`, `ra`, the argument, and `local->suspended`. -/
def prologueLog (sp ra s0 p : BitVec 64) : List WEntry :=
  [((sp - 32#64 + 16#64).toNat, 8, s0), ((sp - 32#64 + 24#64).toNat, 8, ra), ((sp - 32#64 + 8#64).toNat, 8, 1#64),
   (p.toNat, 4, 1#64)]

/-- The words `caml_memprof_renew_minor_sample` reads. -/
structure RenewReads (m : Std.ExtHashMap Nat (BitVec 8)) (dom start trig : BitVec 64) : Prop where
  lambda : bytesVal .ld (read8 m (2147896560#64).toNat) = 0#64
  domainWord : bytesVal .ld (read8 m (2147896584#64).toNat) = dom
  startWord : bytesVal .ld (read8 m (dom + 48#64).toNat) = start
  triggerWord : bytesVal .ld (read8 m (dom + 72#64).toNat) = trig
  idle : bytesVal .lw (read8 m (2147896112#64).toNat) = 0#64

/-- **A call of `caml_memprof_set_suspended(1)`**, sampling off, no pending action. -/
structure SuspendInput (ra sp s0 p dom start trig : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x800295d8#64 c
  stack : gprGet c.σ 2 = some sp
  saved0 : gprGet c.σ 8 = some s0
  arg : gprGet c.σ 10 = some 1#64
  localPtr : bytesVal .ld (read8 c.σ.mem (2147895512#64).toNat) = p
  slot8 : WriteWindow (sp - 32#64 + 8#64) 8
  slot16 : WriteWindow (sp - 32#64 + 16#64) 8
  slot24 : WriteWindow (sp - 32#64 + 24#64) 8
  suspended : WriteWindow p 4
  /-- the first two saves miss `&local` -/
  localApart : OutLRange ((prologueLog sp ra s0 p).take 2) (2147895512#64).toNat 8
  image : ImageOutside (prologueLog sp ra s0 p ++ renewLog (sp - 32#64) 0x800295fc#64 dom start trig)
  /-- what the renewal reads, after the prologue -/
  renewMem : RenewReads (writeLog c.σ.mem (prologueLog sp ra s0 p)) dom start trig
  renewSlot : WriteWindow (sp - 32#64 - 16#64 + 8#64) 8
  startWindow : ReadWindow (dom + 48#64) 8
  triggerWindow : ReadWindow (dom + 72#64) 8
  limitWindow : WriteWindow dom 8
  renewSlotApart : ∀ a ∈ [2147896584#64, dom + 48#64, dom + 72#64, 2147896112#64],
    OutLRange [((sp - 32#64 - 16#64 + 8#64).toNat, 8, 0x800295fc#64)] a.toNat 8
  triggerApart : OutLRange [(triggerAddr.toNat, 8, start)] (dom + 72#64).toNat 8
  /-- `local->suspended` misses the frame slots -/
  suspendedApart : ∀ k ∈ [8, 16, 24], OutLRange [(p.toNat, 4, 1#64)] (sp - 32#64 + BitVec.ofNat 64 k).toNat 8
  /-- the reloads after the call miss the renewal's stores -/
  reloadApart : ∀ k ∈ [8, 16, 24],
    OutLRange (renewLog (sp - 32#64) 0x800295fc#64 dom start trig) (sp - 32#64 + BitVec.ofNat 64 k).toNat 8

/-- **`caml_memprof_set_suspended(1)` returned.** -/
structure SuspendPost (before : Config) (ra sp s0 p dom start trig : BitVec 64) (after : Config) : Prop where
  leaf : LeafInput ra after
  pc : pcOf after = some ra
  stack : gprGet after.σ 2 = some sp
  saved0 : gprGet after.σ 8 = some s0
  memory : after.σ.mem = writeLog before.σ.mem
    (prologueLog sp ra s0 p ++ renewLog (sp - 32#64) 0x800295fc#64 dom start trig)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17] →
    gprGet after.σ n = gprGet before.σ n
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  /-- every register that held a value still does, and `gp` is unchanged -/
  kept : GprsKept before after

theorem slot_nat32 {sp : BitVec 64} (w : WriteWindow (sp - 32#64 + 8#64) 8) {k : Nat} (hk : k ≤ 24) :
    (sp - 32#64 + BitVec.ofNat 64 k).toNat = (sp - 32#64).toNat + k := by
  have := w.upper; have := w.lower
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at *
  omega

/-- **`caml_memprof_set_suspended(1)`.** -/
theorem set_suspended_summary {c : Config} {ra sp s0 p dom start trig : BitVec 64}
    (h : SuspendInput ra sp s0 p dom start trig c) : ∃ d, Steps c d ∧ SuspendPost c ra sp s0 p dom start trig d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  have r8 := regsAt_of h.saved0
  have r10 := regsAt_of h.arg
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have logEq : suspendLog (regsAt c) (suspend_loads c.σ.mem (regsAt c)) = prologueLog sp ra s0 p := by
    simp only [suspendLog, suspend_loads, List.getD_cons_zero, h.localPtr, r1, r2, r8, r10, prologueLog]
  obtain ⟨c1, run1, p1⟩ := (suspend_fast c (regsAt c) l0 (by
      simp only [suspend_input, GHolds, r1, r2, r8, r10]
      exact ⟨h.leaf.raReg, h.stack, h.saved0, h.arg, trivial⟩)
    (by rw [r2]; exact h.slot16) (by rw [r2]; exact h.slot24) (by rw [logEq]; exact h.localApart)
    (by rw [r2]; exact h.slot8) (by rw [h.localPtr]; exact h.suspended)
    (by rw [logEq]; exact imageOutside_sublist (List.sublist_append_left _ _) h.image)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  simp only [suspend_regs, suspend_loads, List.getD_cons_zero, h.localPtr, r1, r2, r10, GHolds] at o1
  obtain ⟨-, g8, g2, g1, g10, -⟩ := o1
  have m1 : c1.σ.mem = writeLog c.σ.mem (prologueLog sp ra s0 p) := by rw [p1.memory, logEq]
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary suspend_call_shape suspend_call_decode c1
    (suspend_call_pins p1.image) p1.good p1.image p1.tick p1.minstret [(2, sp + 18446744073709551584#64), (10, 1#64)]
    ⟨g2, g10, trivial⟩ (by change KeysOK [2, 10]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have spEq : sp + 18446744073709551584#64 = sp - 32#64 := by
    rw [BitVec.sub_eq_add_neg, show (-32#64 : BitVec 64) = 18446744073709551584#64 from by decide]
  have m2 : c2.σ.mem = writeLog c.σ.mem (prologueLog sp ra s0 p) := by rw [p2.memory, m1]
  have reads := h.renewMem
  rw [← m2] at reads
  have renewIn : RenewMinorSample.RenewInput 0x800295fc#64 (sp - 32#64) dom start trig c2 :=
    { leaf := ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
      pc := by have := p2.pc; rw [suspend_call_target] at this; exact this
      stack := by rw [← spEq]; exact gholds_lookup (n := 2) _ p2.regs rfl
      a0 := gpr_some_of (gholds_lookup (n := 10) _ p2.regs rfl)
      lambda := reads.lambda, domainWord := reads.domainWord, startWord := reads.startWord
      triggerWord := reads.triggerWord, idle := reads.idle
      slot := h.renewSlot, startWindow := h.startWindow, triggerWindow := h.triggerWindow
      limitWindow := h.limitWindow
      image := imageOutside_sublist (List.sublist_append_right _ _) h.image
      slotApart := h.renewSlotApart, triggerApart := h.triggerApart }
  obtain ⟨c3, run3, p3⟩ := renew_summary renewIn
  have m3 : c3.σ.mem = writeLog (writeLog c.σ.mem (prologueLog sp ra s0 p))
      (renewLog (sp - 32#64) 0x800295fc#64 dom start trig) := by rw [p3.memory, m2]
  have t8 := slot_nat32 h.slot8 (k := 8) (by decide)
  have t16 := slot_nat32 h.slot8 (k := 16) (by decide)
  have t24 := slot_nat32 h.slot8 (k := 24) (by decide)
  have readSaved : ∀ (i k : Nat) (w : BitVec 64), (prologueLog sp ra s0 p)[i]? = some ((sp - 32#64 + BitVec.ofNat 64 k).toNat, 8, w) →
      k ∈ [8, 16, 24] → OutLRange ((prologueLog sp ra s0 p).drop (i + 1)) (sp - 32#64 + BitVec.ofNat 64 k).toNat 8 →
      bytesVal .ld (read8 c3.σ.mem (sp - 32#64 + BitVec.ofNat 64 k).toNat) = w := by
    intro i k w sel hk out
    rw [m3, read8_writeLog_out _ (h.reloadApart k hk), read8_value]
    exact word_writeLog_at _ _ i _ w sel out
  have pApart := h.suspendedApart
  -- reload the argument: still 1
  have l3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of p3.leaf.raReg]; exact p3.leaf
  have sp3 := p3.stack
  have argBack : bytesVal .ld (read8 c3.σ.mem (sp - 32#64 + 8#64).toNat) = 1#64 :=
    readSaved 2 8 1#64 rfl (by simp) (pApart 8 (by simp))
  obtain ⟨c4, run4, p4⟩ := (resumed_fast c3 (regsAt c3) l3 (by
      simp only [resumed_input, GHolds, regsAt_of sp3]
      exact ⟨sp3, gpr_some p3.a0, trivial⟩)
    (by rw [regsAt_of sp3]; exact h.slot8.read)
    (by simp only [resumed_loads, List.getD_cons_zero, regsAt_of sp3, argBack]; decide)).run c3 ⟨p3.pc, rfl⟩
  have o4 := p4.regs
  simp only [resumed_regs, resumed_loads, List.getD_cons_zero, regsAt_of sp3, argBack, GHolds] at o4
  have k4 : ∀ n, n ≠ 10 → 1 ≤ n → n ≤ 31 → gprGet c4.σ n = gprGet c3.σ n :=
    fun n ne lo hi => p4.gpr_frame (by decide) n lo hi (by simpa using ne)
  have leaf4 : LeafInput 0x800295fc#64 c4 := ⟨p4.good, p4.image, p4.minstret,
    (k4 1 (by decide) (by decide) (by decide)).trans p3.leaf.raReg, by decide, p4.tick⟩
  have l4 : LeafInput (regsAt c4 1) c4 := by rw [regsAt_of leaf4.raReg]; exact leaf4
  have sp4 := (k4 2 (by decide) (by decide) (by decide)).trans sp3
  have m4 : c4.σ.mem = c3.σ.mem := by rw [p4.memory, wl_nil]
  have savedRa : bytesVal .ld (read8 c4.σ.mem (regsAt c4 2 + 24#64).toNat) = ra := by
    rw [regsAt_of sp4, m4]
    exact readSaved 1 24 ra rfl (by simp) (by
      have q := pApart 24 (by simp)
      simp only [prologueLog, List.drop, OutLRange, t8] at q ⊢
      refine ⟨by rw [t24]; omega, q.1, trivial⟩)
  have savedS0 : bytesVal .ld (read8 c4.σ.mem (regsAt c4 2 + 16#64).toNat) = s0 := by
    rw [regsAt_of sp4, m4]
    exact readSaved 0 16 s0 rfl (by simp) (by
      have q := pApart 16 (by simp)
      simp only [prologueLog, List.drop, OutLRange] at q ⊢
      refine ⟨by rw [t16, t24]; omega, by rw [t8, t16]; omega, q.1, trivial⟩)
  obtain ⟨c5, run5, p5⟩ := (leave_fast c4 ra (regsAt c4) l4 (by
      simp only [leave_input, GHolds, regsAt_of sp4, regsAt_of o4.1]; exact ⟨sp4, o4.1, trivial⟩)
    (by rw [regsAt_of sp4]; exact h.slot24.read) (by rw [regsAt_of sp4]; exact h.slot16.read)
    savedRa h.leaf.aligned).run c4 ⟨p4.pc, rfl⟩
  have o5 := p5.regs
  simp only [leave_regs, leave_loads, List.getD_cons_zero, List.getD_cons_succ, GHolds] at o5
  rw [savedRa, savedS0, regsAt_of sp4] at o5
  obtain ⟨s5, s0_5, ra5, -, -⟩ := o5
  refine ⟨c5, run1.trans (run2.trans (run3.trans (run4.trans run5))), ?_⟩
  exact
    { leaf := ⟨p5.good, p5.image, p5.minstret, ra5, h.leaf.aligned, p5.tick⟩
      pc := p5.pc
      stack := by
        have e : sp - 32#64 + 32#64 = sp := by bv_omega
        rw [s5, e]
      saved0 := s0_5
      memory := by rw [p5.memory, wl_nil, m4, m3, ← writeLog_append]
      output := by rw [p5.output, p4.output, p3.output, p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (p5.gpr_frame (by decide) n lo hi (by simp; omega)).trans ((k4 n (by omega) lo hi).trans
          ((p3.frame n lo hi (by simp; omega)).trans ((p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          (p1.gpr_frame (by decide) n lo hi (by simp; omega)))))
      htif := by
        rw [p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          p3.htif, p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)]
      kept := p1.kept.trans (p2.kept.trans (p3.kept.trans (p4.kept.trans p5.kept))) }

end OCaml.Vm.Primitives.Memprof.SetSuspended
