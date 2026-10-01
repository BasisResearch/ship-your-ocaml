import OCaml.Vm.Sim.BinaryArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives
open LeanRV64DExecutable.Functions

/-- RISC-V masks the untagged shift count to its low six bits. -/
theorem shift_count (n : BitVec 63) :
    (Sail.BitVec.extractLsb
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0)) 5 0).toNat =
      n.toNat % 64 := by
  change ((tag64 n).sshiftRight 1).toNat % 64 = n.toNat % 64
  have h := congrArg BitVec.toNat (untag_tag n)
  change ((tag64 n).sshiftRight 1).toNat % 2^63 = n.toNat at h
  omega

/-- Native left shift uses the masked semantic count. -/
theorem shiftLeft_native (x : BitVec 64) (n : BitVec 63) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0)) 5 0) =
      x <<< (n.toNat % 64) := by
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq', shift_count]

/-- Native logical right shift uses the masked semantic count. -/
theorem shiftRight_native (x : BitVec 64) (n : BitVec 63) :
    Sail.shift_bits_right x (Sail.BitVec.extractLsb
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0)) 5 0) =
      x >>> (n.toNat % 64) := by
  simp only [Sail.shift_bits_right, BitVec.ushiftRight_eq', shift_count]

/-- Native arithmetic right shift uses the masked semantic count. -/
theorem shiftArith_native (x : BitVec 64) (n : BitVec 63) :
    shift_bits_right_arith x (Sail.BitVec.extractLsb
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0)) 5 0) =
      x.sshiftRight (n.toNat % 64) := by
  unfold shift_bits_right_arith
  change x.sshiftRight ((Sail.BitVec.extractLsb ((tag64 n).sshiftRight 1) 5 0).toNat) = _
  rw [show (Sail.BitVec.extractLsb ((tag64 n).sshiftRight 1) 5 0).toNat =
    n.toNat % 64 from shift_count n]

/-- Removing the tag makes the native word even. -/
theorem tag_sub_one_even (n : BitVec 63) : (tag64 n - 1#64).toNat % 2 = 0 := by
  rw [BitVec.toNat_sub, tag_toNat]
  have hn := n.isLt
  change ((2^64 - 1 + (2 * n.toNat + 1)) % 2^64) % 2 = 0
  omega

/-- Left shifting an even tagged payload and adding the tag restores an odd word. -/
theorem left_shift_odd (n : BitVec 63) (k : Nat) :
    (((tag64 n - 1#64) <<< k) + 1#64).getLsbD 0 = true := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq]
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  change (((((tag64 n - 1#64).toNat * 2^k) % 2^64) + 1) % 2^64) % 2 = 1
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^64), Nat.add_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 2^64), Nat.mul_mod, tag_sub_one_even]
  simp

end OCaml.Vm.Sim
