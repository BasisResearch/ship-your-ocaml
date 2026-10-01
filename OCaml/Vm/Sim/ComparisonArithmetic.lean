import OCaml.Vm.Sim.BinarySemantics

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode
open LeanRV64DExecutable.Functions

/-- Sail's signed branch guard is the complement of semantic less-than. -/
theorem native_sge (x y : BitVec 64) : zopz0zKzJ_s x y = !x.slt y := by
  apply Bool.eq_iff_iff.mpr
  simp [zopz0zKzJ_s, BitVec.slt]

/-- The reversed strict guard is the complement of semantic signed less-or-equal. -/
theorem native_slt (x y : BitVec 64) : zopz0zI_s x y = !y.sle x := by
  rw [BitVec.sle_eq_not_slt, Bool.not_not]
  rfl

/-- Sail's unsigned guard is the complement of semantic unsigned less-than. -/
theorem native_uge (x y : BitVec 64) : zopz0zKzJ_u x y = !x.ult y := by
  apply Bool.eq_iff_iff.mpr
  simp [zopz0zKzJ_u, BitVec.ult, Sail.BitVec.toNatInt]

/-- Reversed strict unsigned comparison complements semantic less-or-equal. -/
theorem native_ult (x y : BitVec 64) : zopz0zI_u x y = !y.ule x := by
  rw [BitVec.ule_eq_not_ult, Bool.not_not]
  simp [zopz0zI_u, BitVec.ult, Sail.BitVec.toNatInt]

/-- Successful integer comparison supplies its represented arguments and Boolean result. -/
theorem cmpOp_next {s s' : St} {f : BitVec 64 → BitVec 64 → Bool}
    (step : cmpOp s f = .next s') :
    ∃ m n rest, s.accu = .int m ∧ s.stack = .int n :: rest ∧
      {s with pc := s.pc + 1, accu := Val.ofBool (f (tag64 m) (tag64 n)), stack := rest} = s' := by
  cases hs : s.stack with
  | nil => simp [cmpOp, hs] at step
  | cons b rest =>
    cases ha : s.accu <;> cases hb : b <;> simp [cmpOp, hs, ha, hb, ints?, opt] at step
    exact ⟨_, _, rest, rfl, rfl, step⟩

end OCaml.Vm.Sim
