import OCaml.Vm.Sim.Acc0
import OCaml.Vm.Sim.InvariantUse

/-!
# Unconditional ACC rows (pilot)

From the loop-head invariant `LoopAt`, the dispatch code facts, and the
budget's stack bound, the real `ACC0` step is simulated: every premise of
`acc0_arm` is derived (`ArmInput.of_loop`, the selected stack slot from the
step, its read window from `StackGeometry.read`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

theorem opt_next {α : Type} {o : Option α} {k : α → Res} {s' : St} (h : opt o k = .next s') :
    ∃ a, o = some a ∧ k a = .next s' := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- **ACC0 from the loop head.** -/
theorem acc0_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s c .ACC0)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.ACC0, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  have bound : 0 < s.stack.length := (List.getElem?_eq_some_iff.mp selected).1
  exact acc0_arm stable input selected
    ((input.geometry.read input.stack (stack_space input.stack space) bound).window)

end OCaml.Vm.Sim
