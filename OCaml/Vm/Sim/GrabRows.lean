import OCaml.Vm.Sim.GrabFast
import OCaml.Vm.Sim.StackLog

/-!
# Loop-head simulation of GRAB (satisfied-arity path)

When enough extra arguments are pending, GRAB only lowers the extra count.
The partial-application path allocates and is the allocation family's.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **GRAB n from the loop head, satisfied arity.** -/
theorem grab_fast_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .GRAB)
    (fetch : P.code[s.pc + 1]? = some w) (nonnegative : 0 ≤ w.toInt)
    (small : s.extra < 2^63) (enough : w.toInt.toNat ≤ s.extra)
    (step : stepI P s ⟨.GRAB, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨c', run, running⟩ := grab_fast_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch)
    nonnegative small enough step
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
