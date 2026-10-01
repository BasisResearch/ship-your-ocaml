import OCaml.Vm.Sim.ArmInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- A successful abstract relative target is the corresponding nonnegative
integer sum. This applies to ordinary and comparison-branch operand bases. -/
theorem target_int {pc k dest : Nat} {ofs : Int}
    (h : target pc k ofs = some dest) :
    (dest : Int) = pc + 1 + k + ofs := by
  unfold target at h
  dsimp only at h
  split at h
  · cases h
  · have hd := Option.some.inj h
    omega

/-- Map a signed bytecode displacement to the machine's modular byte address.
No placement bound is needed for this algebraic identity. -/
theorem relative_code_word (pl : Place) {pc k dest : Nat} {ofs : Int}
    (h : target pc k ofs = some dest) :
    BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 1 + k)) +
      (BitVec.ofInt 64 ofs <<< (2 : Nat)) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
  have target := target_int h
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 2 = 4#64 from by decide]
  change BitVec.ofInt 64 (↑(pl.codeBase + 4 * (pc + 1 + k))) +
    BitVec.ofInt 64 ofs * BitVec.ofInt 64 4 = BitVec.ofInt 64 (↑(pl.codeBase + 4 * dest))
  rw [← BitVec.ofInt_mul, ← BitVec.ofInt_add]
  apply congrArg (BitVec.ofInt 64)
  omega

end OCaml.Vm.Sim
