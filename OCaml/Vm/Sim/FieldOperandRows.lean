import OCaml.Vm.Sim.Getfield
import OCaml.Vm.Sim.Pushenvacc
import OCaml.Vm.Sim.OperandTableRows

/-!
# GETFIELD n and PUSHENVACC n from the loop head

Field reads with a code operand: the selected field is placed
(`field_selection`) and readable (`StackGeometry.field_read`); PUSHENVACC's
push is `PushWriteOk.of_geometry` in the runtime-stable stack window.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **GETFIELD n from the loop head.** -/
theorem getfield_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .GETFIELD)
    (fetch : P.code[s.pc + 1]? = some w)
    (step : stepI P s ⟨.GETFIELD, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
  replace step := Res.unguard step
  change opt (field? s.heap s.accu w.toInt.toNat)
    (fun v => .next { (s.adv 2) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt (by simp [roots]) selected
  obtain ⟨c', run, running⟩ := getfield_arm stable input (OperandAt.of_fetch input.geometry fetch)
    nonnegative sel (input.geometry.field_read sel)
  exact ⟨c', run, h.of_plus run running⟩

/-- **PUSHENVACC n from the loop head.** -/
theorem pushenvacc_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHENVACC) (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHENVACC, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
  replace step := Res.unguard step
  change opt (field? s.heap s.env w.toInt.toNat)
    (fun v => .next { (pushAccu (s.adv 2)) with accu := v }) = .next s' at step
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨x, -, pushed⟩ := input.accu
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt (by simp [roots]) selected
  obtain ⟨c', run, running⟩ := pushenvacc_arm (by simpa only [Nat.mul_one] using rf.push input space)
    input (PushWriteOk.of_geometry input.geometry input.stack space)
    (OperandAt.of_fetch input.geometry fetch) sel (input.geometry.field_read sel) nonnegative pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- **The GETFIELD n row.** -/
theorem getfield_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .GETFIELD :=
  opArm_of_next1 (fun _ _ _ _ _ _ h code fetch step => getfield_next stable h code fetch step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The PUSHENVACC n row.** -/
theorem pushenvacc_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHENVACC :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      pushenvacc_next rf h code fetch (stack_fits fits capacity reach) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

end OCaml.Vm.Sim
