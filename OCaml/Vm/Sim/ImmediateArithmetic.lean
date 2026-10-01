import OCaml.Vm.Primitives.TagArithmetic

namespace OCaml.Vm.Sim
open OCaml.Bytecode OCaml.Vm.Primitives

/-- The interpreter's `2 - accu` is tagged modular integer negation,
including the minimum signed 63-bit value. -/
theorem tag_neg (n : BitVec 63) : 2#64 - tag64 n = tag64 (-n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, tag_toNat, tag_toNat, BitVec.toNat_neg]
  have hn := n.isLt
  change (2^64 - (2 * n.toNat + 1) + 2) % 2^64 = 2 * ((2^63 - n.toNat) % 2^63) + 1
  omega

/-- Tagged immediates round-trip through the semantics' signed untagging. -/
theorem untag_tag (n : BitVec 63) : untag (tag64 n) = n := by
  unfold untag
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_sshiftRight]
  simp only [tag_toNat, Nat.shiftRight_eq_div_pow]
  have hn := n.isLt
  split <;> omega

/-- The exact NEGINT expression used by `stepI`. -/
theorem untag_neg (n : BitVec 63) : untag (2#64 - tag64 n) = -n := by
  rw [tag_neg, untag_tag]

end OCaml.Vm.Sim
