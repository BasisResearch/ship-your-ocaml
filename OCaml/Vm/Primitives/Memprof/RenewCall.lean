import OCaml.Vm.Primitives.Memprof.RenewMinorSample
import OCaml.Vm.Primitives.Memprof.Eqdf2Call
import OCaml.Vm.Primitives.Memprof.YoungLimitCall
import OCaml.Vm.Sim.StopHalt
import OCaml.Vm.Sim.LogRead

/-!
# `caml_memprof_renew_minor_sample` with sampling off

With `lambda == 0.0` (memprof never started), the sample trigger is the
minor heap's start: `caml_memprof_young_trigger = Caml_state->young_alloc_start`,
then `caml_update_young_limit()` (tail call).
-/

namespace OCaml.Vm.Primitives.Memprof.RenewMinorSample
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives OCaml.Vm.Sim
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of wl_nil gprReg_ne_htif gpr_some gpr_some_of)
open OCaml.Vm.Primitives.Memprof.UpdateYoungLimit (limitValue)

/-- The `caml_memprof_young_trigger` word. -/
abbrev triggerAddr : BitVec 64 := 2147896520#64

/-- The three stores: the saved `ra`, the memprof trigger, the young limit. -/
def renewLog (sp ra dom start trig : BitVec 64) : List WEntry :=
  [((sp - 16#64 + 8#64).toNat, 8, ra), (triggerAddr.toNat, 8, start), (dom.toNat, 8, limitValue trig start)]

/-- **A call of `caml_memprof_renew_minor_sample`** with sampling off and no
pending action. -/
structure RenewInput (ra sp dom start trig : BitVec 64) (c : Config) : Prop where
  leaf : LeafInput ra c
  pc : PCAt 0x80029558#64 c
  stack : gprGet c.σ 2 = some sp
  a0 : (gprGet c.σ 10).isSome
  lambda : bytesVal .ld (read8 c.σ.mem (2147896560#64).toNat) = 0#64
  domainWord : bytesVal .ld (read8 c.σ.mem (2147896584#64).toNat) = dom
  startWord : bytesVal .ld (read8 c.σ.mem (dom + 48#64).toNat) = start
  triggerWord : bytesVal .ld (read8 c.σ.mem (dom + 72#64).toNat) = trig
  idle : bytesVal .lw (read8 c.σ.mem (2147896112#64).toNat) = 0#64
  slot : WriteWindow (sp - 16#64 + 8#64) 8
  startWindow : ReadWindow (dom + 48#64) 8
  triggerWindow : ReadWindow (dom + 72#64) 8
  limitWindow : WriteWindow dom 8
  image : ImageOutside (renewLog sp ra dom start trig)
  /-- the saved `ra` misses the words read afterwards -/
  slotApart : ∀ a ∈ [2147896584#64, dom + 48#64, dom + 72#64, 2147896112#64],
    OutLRange [((sp - 16#64 + 8#64).toNat, 8, ra)] a.toNat 8
  /-- the trigger store misses `young_trigger` -/
  triggerApart : OutLRange [(triggerAddr.toNat, 8, start)] (dom + 72#64).toNat 8

/-- **`caml_memprof_renew_minor_sample` returned.** -/
structure RenewPost (before : Config) (ra sp dom start trig : BitVec 64) (after : Config) : Prop where
  leaf : LeafInput ra after
  pc : pcOf after = some ra
  stack : gprGet after.σ 2 = some sp
  a0 : (gprGet after.σ 10).isSome
  memory : after.σ.mem = writeLog before.σ.mem (renewLog sp ra dom start trig)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ n, 1 ≤ n → n ≤ 31 → n ∉ [1, 2, 10, 11, 12, 13, 14, 15, 16, 17] → gprGet after.σ n = gprGet before.σ n
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes

theorem imageOutside_sub {l1 l2 : List WEntry} (sub : l1.Sublist l2) (h : ImageOutside l2) : ImageOutside l1 :=
  imageOutside_sublist sub h

/-- **`caml_memprof_renew_minor_sample()`** with sampling off. -/
theorem renew_summary {c : Config} {ra sp dom start trig : BitVec 64} (h : RenewInput ra sp dom start trig c) :
    ∃ d, Steps c d ∧ RenewPost c ra sp dom start trig d := by
  have r1 := regsAt_of h.leaf.raReg
  have r2 := regsAt_of h.stack
  -- save ra, load lambda, call __eqdf2(lambda, 0)
  have l0 : LeafInput (regsAt c 1) c := by rw [r1]; exact h.leaf
  have slotLog : compareLog (regsAt c) (compare_loads c.σ.mem (regsAt c)) = [((sp - 16#64 + 8#64).toNat, 8, ra)] := by
    simp only [compareLog, r1, r2]
  obtain ⟨c1, run1, p1⟩ := (compare_fast c (regsAt c) l0 (by
      simp only [compare_input, GHolds, r1, r2]; exact ⟨h.leaf.raReg, h.stack, gpr_some h.a0, trivial⟩)
    (by rw [r2]; exact h.slot)
    (by rw [slotLog]; exact imageOutside_sub (by simp [renewLog]) h.image)).run c ⟨h.pc, rfl⟩
  have o1 := p1.regs
  simp only [compare_regs, compare_loads, List.getD_cons_zero, h.lambda, r1, r2, GHolds] at o1
  obtain ⟨g2, g10, g11, g1, -⟩ := o1
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary compare_call_shape compare_call_decode c1 (compare_call_pins p1.image)
    p1.good p1.image p1.tick p1.minstret [(2, sp + 18446744073709551600#64), (10, 0#64), (11, 0#64)]
    ⟨g2, g10, g11, trivial⟩ (by change KeysOK [2, 10, 11]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c1
    ⟨p1.pc, rfl⟩
  have link : LeafInput 0x80029570#64 c2 :=
    ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
  obtain ⟨c3, run3, p3⟩ := Eqdf2.eqdf2_zero link
    (by have := p2.pc; rw [compare_call_target] at this; exact this)
    (gholds_lookup (n := 10) _ p2.regs rfl) (gholds_lookup (n := 11) _ p2.regs rfl)
  -- lambda == 0.0: the trigger is the minor heap's start
  have l3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of p3.leaf.raReg]; exact p3.leaf
  obtain ⟨c4, run4, p4⟩ := (off_fast c3 (regsAt c3) l3 (by
      simp only [off_input, GHolds, regsAt_of p3.result]; exact ⟨p3.result, trivial⟩)
    (by rw [regsAt_of p3.result]; decide)).run c3 ⟨p3.pc, rfl⟩
  have k4 : ∀ n, 1 ≤ n → n ≤ 31 → gprGet c4.σ n = gprGet c3.σ n :=
    fun n lo hi => p4.gpr_frame (by decide) n lo hi (by simp)
  have sp3 : gprGet c3.σ 2 = some (sp + 18446744073709551600#64) :=
    (p3.frame 2 (by decide) (by decide) (by decide)).trans
      ((p2.gpr_frame (by decide) 2 (by decide) (by decide) (by decide)).trans g2)
  have leaf4 : LeafInput 0x80029570#64 c4 := ⟨p4.good, p4.image, p4.minstret,
    (k4 1 (by decide) (by decide)).trans p3.leaf.raReg, by decide, p4.tick⟩
  have sp4 := (k4 2 (by decide) (by decide)).trans sp3
  have a4 := (k4 10 (by decide) (by decide)).trans p3.result
  have m4 : c4.σ.mem = writeLog c.σ.mem [((sp - 16#64 + 8#64).toNat, 8, ra)] := by
    rw [p4.memory, wl_nil, p3.memory, p2.memory, p1.memory, slotLog]
  have keepSlot : ∀ a ∈ [2147896584#64, dom + 48#64, dom + 72#64, 2147896112#64],
      read8 c4.σ.mem a.toNat = read8 c.σ.mem a.toNat :=
    fun a ha => by rw [m4]; exact read8_writeLog_out _ (h.slotApart a ha)
  have l4 : LeafInput (regsAt c4 1) c4 := by rw [regsAt_of leaf4.raReg]; exact leaf4
  have dom4 : bytesVal .ld (read8 c4.σ.mem (2147896584#64).toNat) = dom := by
    rw [keepSlot _ (by simp)]; exact h.domainWord
  obtain ⟨c5, run5, p5⟩ := (trigger_fast c4 (regsAt c4) l4 (by
      simp only [trigger_input, GHolds, regsAt_of leaf4.raReg, regsAt_of sp4, regsAt_of a4]
      exact ⟨leaf4.raReg, sp4, a4, trivial⟩)
    (by rw [dom4]; exact h.startWindow)).run c4 ⟨p4.pc, rfl⟩
  have o5 := p5.regs
  simp only [trigger_regs, trigger_loads, List.getD_cons_zero, List.getD_cons_succ, dom4,
    keepSlot _ (by simp : dom + 48#64 ∈ [2147896584#64, dom + 48#64, dom + 72#64, 2147896112#64]),
    h.startWord, GHolds] at o5
  obtain ⟨g15, -, -, -, -⟩ := o5
  have k5 : ∀ n, n ≠ 15 → 1 ≤ n → n ≤ 31 → gprGet c5.σ n = gprGet c4.σ n :=
    fun n ne lo hi => p5.gpr_frame (by decide) n lo hi (by simpa using ne)
  have leaf5 : LeafInput 0x80029570#64 c5 := ⟨p5.good, p5.image, p5.minstret,
    (k5 1 (by decide) (by decide) (by decide)).trans leaf4.raReg, by decide, p5.tick⟩
  have l5 : LeafInput (regsAt c5 1) c5 := by rw [regsAt_of leaf5.raReg]; exact leaf5
  have sp5 := (k5 2 (by decide) (by decide) (by decide)).trans sp4
  have a5 := (k5 10 (by decide) (by decide) (by decide)).trans a4
  have m5 : c5.σ.mem = c4.σ.mem := by rw [p5.memory, wl_nil]
  -- restore ra, store the trigger, tail-call caml_update_young_limit
  have spSlot : sp + 18446744073709551600#64 + 8#64 = sp - 16#64 + 8#64 := by
    rw [BitVec.sub_eq_add_neg, show (-16#64 : BitVec 64) = 18446744073709551600#64 from by decide]
  have savedRa : bytesVal .ld (read8 c5.σ.mem (sp - 16#64 + 8#64).toNat) = ra := by
    rw [m5, m4, read8_value]; exact word_writeLog_at _ _ 0 _ ra rfl trivial
  have trigLog : storeLog (regsAt c5) (store_loads c5.σ.mem (regsAt c5)) = [(triggerAddr.toNat, 8, start)] := by
    simp only [storeLog, regsAt_of g15]; rfl
  obtain ⟨c6, run6, p6⟩ := (store_fast c5 (regsAt c5) l5 (by
      simp only [store_input, GHolds, regsAt_of sp5, regsAt_of a5, regsAt_of g15]; exact ⟨sp5, a5, g15, trivial⟩)
    (by rw [regsAt_of sp5, spSlot]; exact h.slot.read)
    (by rw [trigLog]; exact imageOutside_sub (by simp [renewLog]) h.image)).run c5 ⟨p5.pc, rfl⟩
  have o6 := p6.regs
  simp only [store_regs, store_loads, List.getD_cons_zero, regsAt_of sp5, spSlot, savedRa, GHolds] at o6
  obtain ⟨s6, -, ra6, a6, -, -⟩ := o6
  have m6 : c6.σ.mem = writeLog (writeLog c.σ.mem [((sp - 16#64 + 8#64).toNat, 8, ra)]) [(triggerAddr.toNat, 8, start)] := by
    rw [p6.memory, trigLog, m5, m4]
  have spEq : sp + 18446744073709551600#64 + 16#64 = sp := by bv_omega
  rw [spEq] at s6
  have readKept : ∀ a ∈ [2147896584#64, dom + 72#64, 2147896112#64], OutLRange [(triggerAddr.toNat, 8, start)] a.toNat 8 →
      read8 c6.σ.mem a.toNat = read8 c.σ.mem a.toNat := by
    intro a ha out
    rw [m6, read8_writeLog_out _ out]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact read8_writeLog_out _ (h.slotApart _ (by simp))
    · exact read8_writeLog_out _ (h.slotApart _ (by simp))
    · exact read8_writeLog_out _ (h.slotApart _ (by simp))
  have farTrigger : ∀ a : BitVec 64, a = 2147896584#64 ∨ a = 2147896112#64 →
      OutLRange [(triggerAddr.toNat, 8, start)] a.toNat 8 := by
    rintro a (rfl | rfl) <;> simp [OutLRange, triggerAddr]
  have limitIn : UpdateYoungLimit.LimitInput ra dom trig start c6 :=
    { leaf := ⟨p6.good, p6.image, p6.minstret, ra6, h.leaf.aligned, p6.tick⟩
      pc := p6.pc, a0 := gpr_some_of a6
      domain := by rw [readKept _ (by simp) (farTrigger _ (Or.inl rfl))]; exact h.domainWord
      trigger := by rw [readKept _ (by simp) h.triggerApart]; exact h.triggerWord
      memprof := by rw [m6, read8_value]; exact word_writeLog_at _ _ 0 _ start rfl trivial
      triggerWindow := h.triggerWindow, limitWindow := h.limitWindow
      image := imageOutside_sub (by simp [renewLog]) h.image
      idle := by rw [readKept _ (by simp) (farTrigger _ (Or.inr rfl))]; exact h.idle }
  obtain ⟨c7, run7, p7⟩ := UpdateYoungLimit.update_young_limit limitIn
  refine ⟨c7, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))), ?_⟩
  exact
    { leaf := p7.leaf, pc := p7.pc
      stack := (p7.frame 2 (by decide) (by decide) (by decide)).trans s6
      a0 := gpr_some_of ((p7.frame 10 (by decide) (by decide) (by decide)).trans a6)
      memory := by rw [p7.memory, m6, ← writeLog_append, ← writeLog_append]; rfl
      output := by rw [p7.output, p6.output, p5.output, p4.output, p3.output, p2.output, p1.output]
      frame := fun n lo hi out => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at out
        exact (p7.frame n lo hi (by simp; omega)).trans ((p6.gpr_frame (by decide) n lo hi (by simp; omega)).trans
          ((k5 n (by omega) lo hi).trans ((k4 n lo hi).trans ((p3.frame n lo hi (by simp; omega)).trans
          ((p2.gpr_frame (by decide) n lo hi (by simp; omega)).trans (p1.gpr_frame (by decide) n lo hi (by simp; omega)))))))
      htif := by
        rw [p7.htif, p6.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide), p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          p3.htif, p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide),
          p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide)] }

end OCaml.Vm.Primitives.Memprof.RenewMinorSample
