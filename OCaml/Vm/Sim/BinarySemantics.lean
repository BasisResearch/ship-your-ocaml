import OCaml.Vm.Sim.BinaryArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- A successful integer binary step supplies both integer inputs and the
remaining stack. Shared by the generated arithmetic/bitwise arm wrappers. -/
theorem intOp_next {s s' : St} {f : BitVec 64 → BitVec 64 → BitVec 64}
    (step : intOp s f = .next s') :
    ∃ m n rest, s.accu = .int m ∧ s.stack = .int n :: rest ∧
      {s with pc := s.pc + 1, accu := .int (untag (f (tag64 m) (tag64 n))), stack := rest} = s' := by
  cases hs : s.stack with
  | nil => simp [intOp, hs] at step
  | cons b rest =>
    cases ha : s.accu <;> cases hb : b <;> simp [intOp, hs, ha, hb, ints?, opt] at step
    exact ⟨_, _, rest, rfl, rfl, step⟩

end OCaml.Vm.Sim
