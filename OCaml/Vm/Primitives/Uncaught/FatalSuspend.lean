import OCaml.Vm.Primitives.Uncaught.FatalFront
import OCaml.Vm.Primitives.Memprof.SuspendCall
import OCaml.Vm.Primitives.Console.Flush
import OCaml.Vm.Primitives.StringCopyObservations

/-!
# `caml_fatal_uncaught_exception`: `caml_memprof_set_suspended(1)` and the call of `caml_format_exception`

After the handler lookup (`Looked`): `s0 = NULL`, `caml_memprof_set_suspended(1)`
(`set_suspended_summary`), the `beqz s0` to the default handler, and
`caml_format_exception(exn)`'s call. `MemprofAt` names memprof's state at the
entry; its three stores (the suspended flag, the young trigger, the domain's
`young_limit`) are the only change below `heapEnd` (`AtFormat.kept`).
-/

namespace OCaml.Vm.Primitives.Uncaught.FatalUncaught
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Vsa.MemRepr LeanRV64DExecutable OCaml.Bytecode OCaml.Vm.Primitives
  OCaml.Vm.Boot.Startup OCaml.Vm.Sim
open OCaml.Vm.Primitives.Named.NamedValue (regsAt regsAt_of gpr_some gpr_some_of gprReg_ne_htif)
open OCaml.Vm.Primitives.Memprof.SetSuspended (prologueLog RenewReads SuspendInput SuspendPost set_suspended_summary)
open OCaml.Vm.Primitives.Memprof.RenewMinorSample (renewLog triggerAddr)
open OCaml.Vm.Primitives.Memprof.UpdateYoungLimit (limitValue)

/-- memprof's three stores: the suspended flag, the young trigger, the domain's `young_limit`. -/
def memprofStores (p dom start trig : BitVec 64) : List WEntry :=
  [(p.toNat, 4, 1#64), (triggerAddr.toNat, 8, start), (dom.toNat, 8, limitValue trig start)]

/-- **memprof at the entry**: sampling off (`lambda = 0`), no pending action,
the context pointer `p`, the domain record `dom`, and where the three stores
land (in RAM below `heapEnd`, above `.rodata`, apart from what is read). -/
structure MemprofAt (m : Mem) (p dom start trig : BitVec 64) : Prop where
  localPtr : bytesVal .ld (read8 m (2147895512#64).toNat) = p
  reads : RenewReads m dom start trig
  suspended : WriteWindow p 4
  startWindow : ReadWindow (dom + 48#64) 8
  triggerWindow : ReadWindow (dom + 72#64) 8
  limitWindow : WriteWindow dom 8
  triggerApart : OutLRange [(triggerAddr.toNat, 8, start)] (dom + 72#64).toNat 8
  /-- the flag store misses `local` and the renewal's reads -/
  flagApart : ∀ a ∈ [2147895512#64, 2147896560#64, 2147896584#64, dom + 48#64, dom + 72#64, 2147896112#64],
    OutLRange [(p.toNat, 4, 1#64)] a.toNat 8
  pHigh : p.toNat + 4 ≤ heapEnd
  domHigh : dom.toNat + 80 ≤ heapEnd
  pLow : Image.rodataBase + Image.rodataSize ≤ p.toNat
  domLow : Image.rodataBase + Image.rodataSize ≤ dom.toNat

/-- At `caml_format_exception`'s entry. -/
structure AtFormat (before : Config) (sp exn s2 s3 : BitVec 64) (p dom start trig : BitVec 64) (f : Config) :
    Prop where
  leaf : LeafInput 0x8000dfc8#64 f
  ready : LibraryReady f
  pc : PCAt 0x8000dbec#64 f
  stack : gprGet f.σ 2 = some (sp + 18446744073709551568#64)
  arg : gprGet f.σ 10 = some exn
  saved0 : gprGet f.σ 8 = some 0#64
  saved1 : gprGet f.σ 9 = some exn
  saved2 : gprGet f.σ 18 = some s2
  saved3 : gprGet f.σ 19 = some s3
  callee : ∀ k, 20 ≤ k → k ≤ 27 → gprGet f.σ k = gprGet before.σ k
  /-- below `heapEnd`, only memprof's stores changed -/
  kept : ∀ a, a < heapEnd → OutL (memprofStores p dom start trig) a → f.σ.mem[a]? = before.σ.mem[a]?
  output : Vsa.Machine.output f.σ = Vsa.Machine.output before.σ

/-- The renewal's return-address slot, below the lookup frames. -/
theorem renew_slot {sp : BitVec 64} (frame : NativeFrame sp 128) :
    (sp + 18446744073709551568#64 - 32#64 - 16#64 + 8#64).toNat = nativeFrameBase sp 128 + 40 := by
  have base := fatal_sp frame
  have hiS := frame.upper
  have hB : nativeFrameBase sp 128 + 128 = sp.toNat := by
    have := Nat.le_trans (Nat.le_add_left _ _) frame.lower; unfold nativeFrameBase; omega
  simp only [Layout.sym_stack_top] at hiS
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, base, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem dom_off {dom : BitVec 64} (high : dom.toNat + 80 ≤ heapEnd) (k : Nat) (hk : k ≤ 80) :
    (dom + BitVec.ofNat 64 k).toNat = dom.toNat + k := by
  have : heapEnd < 2 ^ 64 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **`caml_memprof_set_suspended(1)`, the default-handler branch and the call
`caml_format_exception(exn)`.** -/
theorem fatal_suspend {sp exn s0 s2 s3 p dom start trig : BitVec 64} {c0 d : Config}
    (frame : NativeFrame sp 128) (look : Looked c0 sp exn s0 s2 s3 d) (mp : MemprofAt c0.σ.mem p dom start trig) :
    ∃ f, Steps d f ∧ AtFormat c0 sp exn s2 s3 p dom start trig f := by
  have fp := fatal_sp frame
  have hB : nativeFrameBase sp 128 + 128 = sp.toNat := by
    have := Nat.le_trans (Nat.le_add_left _ _) frame.lower; unfold nativeFrameBase; omega
  have hE : heapEnd ≤ nativeFrameBase sp 128 := by have := frame.lower; omega
  have lslot (k : Nat) (hk : k ≤ 32) :
      (sp + 18446744073709551568#64 - 32#64 + BitVec.ofNat 64 k).toNat = nativeFrameBase sp 128 + (48 + k) :=
    lookup_slot frame k hk
  have rslot := renew_slot frame
  have pH := mp.pHigh
  have dH := mp.domHigh
  have d48 := dom_off mp.domHigh 48 (by decide)
  have d72 := dom_off mp.domHigh 72 (by decide)
  have hEv : heapEnd = 2256535552 := rfl
  -- the suspend block: s0 = NULL, a0 = 1
  have r1 := regsAt_of look.leaf.raReg
  have r10 := regsAt_of look.result
  have l0 : LeafInput (regsAt d 1) d := by rw [r1]; exact look.leaf
  obtain ⟨c1, run1, p1⟩ := (suspend_fast d (regsAt d) l0 (by
      simp only [suspend_input, GHolds, r1, r10]; exact ⟨look.leaf.raReg, look.result, trivial⟩)).run d ⟨look.pc, rfl⟩
  have o1 := p1.regs
  simp only [suspend_regs, suspend_loads, r1, r10, GHolds] at o1
  obtain ⟨g10, g8, -, -⟩ := o1
  have k1 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [8, 10]) : gprGet c1.σ n = gprGet d.σ n :=
    p1.gpr_frame (by decide) n lo hi out
  obtain ⟨c2, run2, p2⟩ := (call_registers_summary suspend_call_shape suspend_call_decode c1
    (suspend_call_pins p1.image) p1.good p1.image p1.tick p1.minstret
    [(10, 1#64), (8, 0#64), (2, sp + 18446744073709551568#64), (9, exn), (18, s2), (19, s3)]
    ⟨g10, g8, (k1 2 (by decide) (by decide) (by decide)).trans look.stack,
      (k1 9 (by decide) (by decide) (by decide)).trans look.exn,
      (k1 18 (by decide) (by decide) (by decide)).trans look.saved2,
      (k1 19 (by decide) (by decide) (by decide)).trans look.saved3, trivial⟩
    (by change KeysOK [10, 8, 2, 9, 18, 19]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c1 ⟨p1.pc, rfl⟩
  have m2 : c2.σ.mem = d.σ.mem := by rw [p2.memory, p1.memory, Named.NamedValue.wl_nil]
  have low2 : LowSame c0.σ.mem c2.σ.mem := fun a ha => by rw [m2]; exact look.low a ha
  have rd (A : Nat) (hA : A + 8 ≤ heapEnd) : read8 c2.σ.mem A = read8 c0.σ.mem A :=
    ConsoleWrite.read8_same fun i hi => by rw [low2 _ (by omega)]
  -- the prologue's stores miss what the renewal reads
  have apartP (X : Nat) (hX : OutLRange [(p.toNat, 4, 1#64)] X 8) (hXlow : X + 8 ≤ heapEnd) :
      OutLRange (prologueLog (sp + 18446744073709551568#64) 0x8000df84#64 0#64 p) X 8 := by
    simp only [prologueLog, OutLRange, lslot 16 (by decide), lslot 24 (by decide), lslot 8 (by decide)]
    exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), hX.1, trivial⟩
  have readP (X : Nat) (hX : OutLRange [(p.toNat, 4, 1#64)] X 8) (hXlow : X + 8 ≤ heapEnd) :
      read8 (writeLog c2.σ.mem (prologueLog (sp + 18446744073709551568#64) 0x8000df84#64 0#64 p)) X =
        read8 c0.σ.mem X := by
    rw [OCaml.Vm.Sim.read8_writeLog_out _ (apartP X hX hXlow), rd X hXlow]
  have flag (a : BitVec 64) (ha : a ∈ [2147895512#64, 2147896560#64, 2147896584#64, dom + 48#64, dom + 72#64,
      2147896112#64]) := mp.flagApart a ha
  have susp : SuspendInput 0x8000df84#64 (sp + 18446744073709551568#64) 0#64 p dom start trig c2 :=
    { leaf := ⟨p2.good, p2.image, p2.minstret, gholds_lookup (n := 1) _ p2.regs rfl, by decide, p2.tick⟩
      pc := by have := p2.pc; rw [suspend_call_target] at this; exact this
      stack := gholds_lookup (n := 2) _ p2.regs rfl
      saved0 := gholds_lookup (n := 8) _ p2.regs rfl
      arg := gholds_lookup (n := 10) _ p2.regs rfl
      localPtr := by rw [rd _ (by rw [hEv]; decide)]; exact mp.localPtr
      slot8 := fatal_slot frame (lslot 8 (by decide)) (by decide) (by decide)
      slot16 := fatal_slot frame (lslot 16 (by decide)) (by decide) (by decide)
      slot24 := fatal_slot frame (lslot 24 (by decide)) (by decide) (by decide)
      suspended := mp.suspended
      localApart := by
        simp only [prologueLog, List.take, OutLRange, lslot 16 (by decide), lslot 24 (by decide)]
        refine ⟨Or.inl ?_, Or.inl ?_, trivial⟩ <;> simp only [BitVec.toNat_ofNat] <;> omega
      image := by
        have pL := mp.pLow
        have dL := mp.domLow
        constructor <;>
          simp only [prologueLog, renewLog, List.cons_append, List.nil_append, OutLRange, lslot 16 (by decide),
            lslot 24 (by decide), lslot 8 (by decide), rslot, triggerAddr, BitVec.toNat_ofNat] <;>
          simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] at pL dL ⊢ <;>
          refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, trivial⟩ <;> omega
      renewMem :=
        { lambda := by rw [readP _ (flag _ (by simp)) (by rw [hEv]; decide)]; exact mp.reads.lambda
          domainWord := by rw [readP _ (flag _ (by simp)) (by rw [hEv]; decide)]; exact mp.reads.domainWord
          startWord := by rw [readP _ (flag _ (by simp)) (by rw [d48]; omega)]; exact mp.reads.startWord
          triggerWord := by rw [readP _ (flag _ (by simp)) (by rw [d72]; omega)]; exact mp.reads.triggerWord
          idle := by rw [readP _ (flag _ (by simp)) (by rw [hEv]; decide)]; exact mp.reads.idle }
      renewSlot := fatal_slot frame rslot (by decide) (by decide)
      startWindow := mp.startWindow
      triggerWindow := mp.triggerWindow
      limitWindow := mp.limitWindow
      renewSlotApart := fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> simp only [OutLRange, rslot, d48, d72, BitVec.toNat_ofNat] <;>
          exact ⟨Or.inl (by omega), trivial⟩
      triggerApart := mp.triggerApart
      suspendedApart := fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp only [OutLRange, lslot 8 (by decide), lslot 16 (by decide),
          lslot 24 (by decide)] <;> exact ⟨Or.inr (by omega), trivial⟩
      reloadApart := fun k hk => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> simp only [renewLog, OutLRange, rslot, lslot 8 (by decide),
          lslot 16 (by decide), lslot 24 (by decide), triggerAddr, BitVec.toNat_ofNat] <;>
          exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), trivial⟩ }
  obtain ⟨c3, run3, p3⟩ := set_suspended_summary susp
  -- the default handler: `beqz s0`
  have a10 : gprGet c3.σ 10 = some (regsAt c3 10) :=
    gpr_some (p3.kept.present 10 (by decide) (by decide) (by rw [gholds_lookup (n := 10) _ p2.regs rfl]; rfl))
  have r3_8 := regsAt_of p3.saved0
  have l3 : LeafInput (regsAt c3 1) c3 := by rw [regsAt_of p3.leaf.raReg]; exact p3.leaf
  obtain ⟨c4, run4, p4⟩ := (absent_fast c3 (regsAt c3) l3 (by
      simp only [absent_input, GHolds, r3_8]; exact ⟨p3.saved0, a10, trivial⟩)
    (by rw [r3_8]; decide)).run c3 ⟨p3.pc, rfl⟩
  have k4 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet c4.σ n = gprGet c3.σ n :=
    p4.gpr_frame (by decide) n lo hi (by simp)
  have k3 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17]) :
      gprGet c3.σ n = gprGet c2.σ n := p3.frame n lo hi out
  have e9 : gprGet c4.σ 9 = some exn :=
    (k4 9 (by decide) (by decide)).trans ((k3 9 (by decide) (by decide) (by decide)).trans
      (gholds_lookup (n := 9) _ p2.regs rfl))
  have e1 : gprGet c4.σ 1 = some 0x8000df84#64 := (k4 1 (by decide) (by decide)).trans p3.leaf.raReg
  have l4 : LeafInput (regsAt c4 1) c4 := by
    rw [regsAt_of e1]; exact ⟨p4.good, p4.image, p4.minstret, e1, by decide, p4.tick⟩
  -- a0 = exn; call caml_format_exception
  obtain ⟨c5, run5, p5⟩ := (format_fast c4 (regsAt c4) l4 (by
      simp only [format_input, GHolds, regsAt_of e1, regsAt_of e9]; exact ⟨e1, e9, trivial⟩)).run c4 ⟨p4.pc, rfl⟩
  have o5 := p5.regs
  simp only [format_regs, format_loads, regsAt_of e1, regsAt_of e9, GHolds] at o5
  obtain ⟨f10, -, f9, -⟩ := o5
  have k5 (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [10]) : gprGet c5.σ n = gprGet c4.σ n :=
    p5.gpr_frame (by decide) n lo hi out
  have via (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) (out : n ∉ [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17]) :
      gprGet c5.σ n = gprGet c2.σ n :=
    (k5 n lo hi (fun m => out (by simp at m; simp [m]))).trans ((k4 n lo hi).trans (k3 n lo hi out))
  obtain ⟨c6, run6, p6⟩ := (call_registers_summary format_call_shape format_call_decode c5
    (format_call_pins p5.image) p5.good p5.image p5.tick p5.minstret
    [(10, exn), (9, exn), (2, sp + 18446744073709551568#64), (8, 0#64), (18, s2), (19, s3)]
    ⟨f10, f9, (k5 2 (by decide) (by decide) (by decide)).trans ((k4 2 (by decide) (by decide)).trans p3.stack),
      (k5 8 (by decide) (by decide) (by decide)).trans ((k4 8 (by decide) (by decide)).trans p3.saved0),
      (via 18 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 18) _ p2.regs rfl),
      (via 19 (by decide) (by decide) (by decide)).trans (gholds_lookup (n := 19) _ p2.regs rfl), trivial⟩
    (by change KeysOK [10, 9, 2, 8, 18, 19]; decide) (by simp [KeysAvoidRa, keysG]) rfl).run c5 ⟨p5.pc, rfl⟩
  have m6 : c6.σ.mem = writeLog d.σ.mem (prologueLog (sp + 18446744073709551568#64) 0x8000df84#64 0#64 p ++
      renewLog (sp + 18446744073709551568#64 - 32#64) 0x800295fc#64 dom start trig) := by
    rw [p6.memory, p5.memory, Named.NamedValue.wl_nil, p4.memory, Named.NamedValue.wl_nil, p3.memory, m2]
  refine ⟨c6, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))), ?_⟩
  exact
    { leaf := ⟨p6.good, p6.image, p6.minstret, gholds_lookup (n := 1) _ p6.regs rfl, by decide, p6.tick⟩
      ready := (((((look.ready.carry p1.kept (p1.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p2.kept
        (p2.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p3.kept p3.htif).carry p4.kept
        (p4.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p5.kept
        (p5.frame _ (fun n _ => gprReg_ne_htif n) (by decide))).carry p6.kept
        (p6.frame _ (fun n _ => gprReg_ne_htif n) (by decide))
      pc := by have := p6.pc; rw [format_call_target] at this; exact this
      stack := gholds_lookup (n := 2) _ p6.regs rfl
      arg := gholds_lookup (n := 10) _ p6.regs rfl
      saved0 := gholds_lookup (n := 8) _ p6.regs rfl
      saved1 := gholds_lookup (n := 9) _ p6.regs rfl
      saved2 := gholds_lookup (n := 18) _ p6.regs rfl
      saved3 := gholds_lookup (n := 19) _ p6.regs rfl
      callee := fun k lo hi => by
        have out : k ∉ [1, 2, 8, 10, 11, 12, 13, 14, 15, 16, 17] := by simp; omega
        exact (p6.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
          ((via k (by omega) (by omega) out).trans ((p2.gpr_frame (by decide) k (by omega) (by omega) (by simp; omega)).trans
            ((k1 k (by omega) (by omega) (by simp; omega)).trans (look.callee k lo hi))))
      kept := fun a ha out => by
        rw [m6, writeLog_out _ _ _ ?_, look.low a ha]
        simp only [memprofStores, OutL] at out
        rw [StringCopy.outL_append_iff]
        simp only [prologueLog, renewLog, OutL, lslot 16 (by decide), lslot 24 (by decide), lslot 8 (by decide), rslot]
        exact ⟨⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), out.1, trivial⟩,
          ⟨Or.inl (by omega), out.2.1, out.2.2.1, trivial⟩⟩
      output := by
        rw [← look.output]
        simp only [Vsa.Machine.output]
        rw [p6.output, p5.output, p4.output, p3.output, p2.output, p1.output] }

end OCaml.Vm.Primitives.Uncaught.FatalUncaught
