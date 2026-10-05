import OCaml.Vm.Sim.StopHalt
import OCaml.Refinement

/-!
# STOP's native preconditions from the loop invariant

At any loop head, `Running.native` gives an entry snapshot `D` with
`Invocation D c ∧ NativeValid D`, and `Running.stack` gives the `Caml_state`
placement. `stop_ready` turns them into the STOP arm's native invocation
(`StopInvocation`) and its caller readiness (`StopCallerReady`): the
interpreter's and caml_main's saved frames are read at `D.nativeSp`, their
return addresses are `NativeValid`'s, and STOP's three runtime stores
(`caml_callback_depth`, `extern_sp`, `external_raise`) lie below the native
stack, apart from the image.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The saved words of the interpreter's frame at `sp`. -/
def interpSavedAt (c : Config) (sp : Nat) : Nat → BitVec 64 :=
  fun r => word c (sp + Layout.interpSaveOffset r)

/-- The saved words of caml_main's frame above the interpreter frame at `sp`. -/
def mainSavedAt (c : Config) (sp : Nat) : Nat → BitVec 64 :=
  fun r => word c (sp + Layout.interpFrameBytes + Layout.camlMainSaveOffset r)

/-- Close an address goal about the native frames and STOP's stores. -/
macro "stop_tac" : tactic =>
  `(tactic| ((try simp only [Vsa.Sim.OutLRange, stopLog, OCaml.Vm.Layout.interpSavedRegs,
      OCaml.Vm.Layout.camlMainSavedRegs, OCaml.Vm.Layout.interpSaveOffset, OCaml.Vm.Layout.camlMainSaveOffset,
      OCaml.Vm.Layout.interpFrameBytes, OCaml.Vm.Layout.sym_caml_callback_depth,
      OCaml.Vm.Layout.off_extern_sp, OCaml.Vm.Layout.off_external_raise, Vsa.Sim.tohostAddr,
      Vsa.Sim.LibraryLayout.tohostAddr, OCaml.Vm.Layout.sym_tohost, Image.textBase, Image.textSize,
      Image.rodataBase, Image.rodataSize, List.mem_cons, List.mem_nil_iff, or_false, and_true,
      forall_eq_or_imp, forall_eq] at *) <;> omega))

/-- **STOP's native preconditions** at a loop head with a given snapshot. -/
theorem stop_ready {c : Config} {D : InvocationData} {vmSp : BitVec 64}
    (inv : Invocation D c) (valid : NativeValid D)
    (dLow : Layout.sym_bss_end ≤ (word c Layout.sym_Caml_state).toNat)
    (dHigh : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd)
    (dAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0) :
    StopInvocation D.nativeSp (interpSavedAt c D.nativeSp) vmSp c ∧
      ∀ value, value &&& 3#64 ≠ 2#64 →
        StopCallerReady D.nativeSp (interpSavedAt c D.nativeSp) (mainSavedAt c D.nativeSp) value vmSp c := by
  have n1 := valid.low
  have n2 := valid.high
  have n3 := valid.aligned
  simp only [Vsa.Sim.DlHeap.heapEnd, Layout.interpFrameBytes, Layout.camlMainFrameBytes,
    Layout.sym_stack_top] at n1 n2
  simp only [Layout.sym_bss_end, Layout.domainStateBytes, Vsa.Sim.DlHeap.heapEnd] at dLow dHigh
  have ra : interpSavedAt c D.nativeSp 1 = 0x80004ff8#64 := valid.interpReturn c inv
  have mra : mainSavedAt c D.nativeSp 1 = 0x80001df0#64 := valid.mainReturn c inv
  refine ⟨⟨⟨fun r _ => rfl, fun r hr => ⟨?_, ?_, ?_⟩⟩, inv.stack, by rw [ra]; decide,
    ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by stop_tac, by stop_tac, by stop_tac⟩, ⟨by stop_tac, by stop_tac, by stop_tac, by stop_tac⟩,
    ⟨by stop_tac, by stop_tac, by stop_tac, by stop_tac⟩, by stop_tac, ⟨by stop_tac, by stop_tac⟩,
    fun r hr => by revert r hr; stop_tac⟩, fun value ordinary => ⟨ra, mra, ordinary,
    ⟨fun r _ => rfl, fun r hr => ⟨?_, ?_, ?_⟩⟩, fun r hr => by revert r hr; stop_tac⟩⟩
  all_goals (revert r hr; stop_tac)

/-- **STOP's exit continuation** at a loop head: the native returns through
caml_interprete and caml_main, then caml_do_exit(0) halts with the console. -/
theorem stop_exit_continuation {c : Config} {D : InvocationData} {vmSp value : BitVec 64}
    (inv : Invocation D c) (valid : NativeValid D)
    (dLow : Layout.sym_bss_end ≤ (word c Layout.sym_Caml_state).toNat)
    (dHigh : (word c Layout.sym_Caml_state).toNat + Layout.domainStateBytes ≤ Vsa.Sim.DlHeap.heapEnd)
    (dAligned : (word c Layout.sym_Caml_state).toNat % 8 = 0)
    (ordinary : value &&& 3#64 ≠ 2#64) (exit : StopExitReady c D.nativeSp vmSp) :
    StopExitContinuation c D.nativeSp (interpSavedAt c D.nativeSp) value vmSp (output c.σ) :=
  stop_exit_continuation_of_do_exit ((stop_ready inv valid dLow dHigh dAligned).2 value ordinary)
    (stop_do_exit_summary exit)

end OCaml.Vm.Sim

namespace OCaml.Vm.Sim
open OCaml.Bytecode

/-- The low two bits of a word, as a natural number. -/
theorem and3_toNat (w : BitVec 64) : (w &&& 3#64).toNat = w.toNat % 4 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 2

/-- **No represented value looks like an exception result** under a
word-aligned placement: ints are odd, pointers, code pointers and atoms are
multiples of four. Only `.raw` words are unconstrained (`GoodF1.stopAccu`). -/
theorem valWord_ordinary {pl : Place} {v : Val} {w : BitVec 64}
    (code : pl.codeBase % 4 = 0) (heap : ∀ l a, pl.φ l = some a → a % 4 = 0)
    (atoms : pl.atomBase % 4 = 0) (notRaw : ∀ r, v ≠ .raw r)
    (hv : valWord pl v = some w) : w &&& 3#64 ≠ 2#64 := by
  intro h2
  have e := congrArg BitVec.toNat h2
  rw [and3_toNat] at e
  simp only [BitVec.toNat_ofNat] at e
  cases v with
  | int n =>
    simp only [valWord, Option.some.injEq] at hv
    subst hv
    have odd : (tag64 n).getLsbD 0 = true := by simp [tag64]
    have odd' : (tag64 n).toNat % 2 = 1 := by
      simpa [BitVec.getLsbD, Nat.testBit_zero] using odd
    omega
  | ptr l k =>
    simp only [valWord, Option.map_eq_some_iff] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    have := heap l a ha
    simp only [BitVec.toNat_ofNat] at e
    omega
  | code pc =>
    simp only [valWord, Option.some.injEq] at hv
    subst hv
    simp only [BitVec.toNat_ofNat] at e
    omega
  | atom t =>
    simp only [valWord, Option.some.injEq] at hv
    subst hv
    simp only [BitVec.toNat_ofNat] at e
    omega
  | raw r => exact notRaw r rfl

end OCaml.Vm.Sim
