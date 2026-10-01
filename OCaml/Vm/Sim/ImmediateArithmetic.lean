import OCaml.Vm.Primitives.TagArithmetic

namespace OCaml.Vm.Sim
open OCaml.Bytecode OCaml.Vm.Primitives

/-- Sign-extending a bytecode operand and tagging it agrees with the
semantics' conversion of its signed 32-bit value to a 63-bit integer. -/
theorem tag_word32 (w : BitVec 32) :
    (w.signExtend 64 <<< (1 : Nat)) + 1#64 = tag64 (BitVec.ofInt 63 w.toInt) := by
  have extend : (w.signExtend 63).signExtend 64 = w.signExtend 64 :=
    congrArg (BitVec.ofInt 64) (BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 63))
  change (w.signExtend 64 <<< (1 : Nat)) + 1#64 =
    (((w.signExtend 63).signExtend 64) <<< (1 : Nat)) ||| 1#64
  rw [extend]
  have tagged := @BitVec.shiftLeft_add_eq_shiftLeft_or 64 1#64 (w.signExtend 64)
  rw [BitVec.shiftLeft_eq'] at tagged
  exact tagged

/-- Tagged modular subtraction, shared by unary and binary integer arms. -/
theorem tag_sub (m n : BitVec 63) : tag64 m + 1#64 - tag64 n = tag64 (m - n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_add, tag_toNat, tag_toNat, tag_toNat, BitVec.toNat_sub]
  have hm := m.isLt
  have hn := n.isLt
  change (2^64 - (2 * n.toNat + 1) + ((2 * m.toNat + 1 + 1) % 2^64)) % 2^64 =
    2 * ((2^63 - n.toNat + m.toNat) % 2^63) + 1
  omega

/-- The interpreter's `2 - accu` is tagged modular integer negation,
including the minimum signed 63-bit value. -/
theorem tag_neg (n : BitVec 63) : 2#64 - tag64 n = tag64 (-n) := by
  simpa only [show tag64 0 + 1#64 = 2#64 from rfl, show (0 : BitVec 63) - n = -n from rfl] using tag_sub 0 n

/-- BOOLNOT implements the runtime's modular `Val_not`, including non-booleans. -/
theorem tag_not (n : BitVec 63) : 4#64 - tag64 n = tag64 (1 - n) := by
  simpa only [show tag64 1 + 1#64 = 4#64 from rfl] using tag_sub 1 n

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
