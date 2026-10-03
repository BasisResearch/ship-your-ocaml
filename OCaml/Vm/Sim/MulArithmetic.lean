import OCaml.Vm.Sim.BinaryArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives

/-- Retagging a native word depends only on its low 63 bits. -/
theorem tag_truncate (w : BitVec 64) :
    tag64 (w.truncate 63) = (w <<< 1) + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [tag_toNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change 2 * (w.toNat % 2^63) + 1 = (w.toNat * 2 % 2^64 + 1) % 2^64
  omega

/-- MULINT's signed native operands and modular libgcc product retag to the
63-bit bytecode product, including overflow and negative inputs. -/
theorem tag_mul_native (m n : BitVec 63) :
    (((tag64 n).sshiftRight 1 * (tag64 m).sshiftRight 1) <<< 1) + 1#64 =
      tag64 (m * n) := by
  rw [← tag_truncate, BitVec.truncate_eq_setWidth, BitVec.setWidth_mul _ _ (by decide)]
  change tag64 (untag (tag64 n) * untag (tag64 m)) = _
  rw [untag_tag, untag_tag, BitVec.mul_comm]

end OCaml.Vm.Sim
