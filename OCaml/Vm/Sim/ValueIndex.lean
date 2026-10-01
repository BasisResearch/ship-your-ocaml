import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives LeanRV64DExecutable.Functions

/-- Scaling by eight removes the sign-extension difference modulo 2^64.
Unlike unscaled byte indexing, this holds for every represented 63-bit index. -/
theorem value_index_word (n : BitVec 63) :
    Sail.shift_bits_left
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0))
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (8 * n.toNat) := by
  have h := congrArg BitVec.toNat (untag_tag n)
  change ((tag64 n).sshiftRight 1).toNat % 2^63 = n.toNat at h
  change ((tag64 n).sshiftRight 1 <<< (3 : Nat)) = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- A RAM-sized byte index is in the nonnegative tagged-integer range. -/
theorem value_byte_index (n : BitVec 63) (small : n.toNat < 2^62) :
    shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0) =
      BitVec.ofNat 64 n.toNat := by
  change (tag64 n).sshiftRight 1 = _
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight]
  simp only [BitVec.msb_eq_decide, tag_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, decide_eq_true_eq]
  split <;> omega

/-- Unsigned byte loads followed by the native tag operation represent the byte. -/
theorem byte_tag (b : BitVec 8) :
    Sail.shift_bits_left (LeanRV64DExecutable.zero_extend (m := 64) b) (Sail.BitVec.extractLsb (0x01#6) 5 0) + 1#64 =
      tag64 (BitVec.ofNat 63 b.toNat) := by
  change (b.setWidth 64 <<< (1 : Nat)) + 1#64 = _
  apply BitVec.eq_of_toNat_eq
  have bound := b.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, tag_toNat]
  omega

end OCaml.Vm.Sim
