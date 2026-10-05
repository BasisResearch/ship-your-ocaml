import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.InvariantUse
import OCaml.RefinementF1

/-!
# Shared lemmas for unconditional stack rows

From the loop-head invariant `LoopAt`, the dispatch code facts and the
budget's stack bound, a stack-read step is simulated: every premise of a generated
stack-read arm is derived (`ArmInput.of_loop`, the selected stack slot from
the step, its read window from `StackGeometry.read`). The generated rows
(`AccRows.lean`) package one F1 table row (`OpArm`) per opcode.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

theorem opt_next {α : Type} {o : Option α} {k : α → Res} {s' : St} (h : opt o k = .next s') :
    ∃ a, o = some a ∧ k a = .next s' := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- A continuation that always steps never halts. -/
theorem opt_not_halt {α : Type} {o : Option α} {k : α → St} {e : Nat} {w : World} :
    opt o (fun a => .next (k a)) ≠ .halt e w := by
  cases o <;> simp [opt]

/-- The budget bounds every reachable stack by the VM stack allocation. -/
theorem stack_fits {B : OCaml.Budget} {P : Prog} {s : St} (fits : OCaml.Fits B P)
    (capacity : 8 * B.stackWords ≤ Layout.stackBytes) (reach : Reach P s) :
    8 * s.stack.length ≤ Layout.stackBytes := by
  have := (fits s reach).1
  omega

/-- Shared simulation of a stack read `ACCn` from the loop head. -/
theorem stack_read_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n : Nat}
    (arm : ∀ pl cp sp high v, ArmInput L P s op c pl cp sp high → s.stack[n]? = some v →
      ReadWindow (BitVec.ofNat 64 (sp + 8 * n)) 8 →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P {s with pc := s.pc + 1, accu := v} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s c op)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : opt (s.stack[n]?) (fun v => .next { (s.adv 1) with accu := v }) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  have bound : n < s.stack.length := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨c', run, running⟩ := arm pl cp sp high v input selected
    ((input.geometry.read input.stack (stack_space input.stack space) bound).window)
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
