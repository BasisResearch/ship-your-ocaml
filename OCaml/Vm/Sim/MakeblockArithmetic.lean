import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.BlockAllocation

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- MAKEBLOCK's unsigned tag conversion agrees with a bounded bytecode tag. -/
theorem makeblock_tag_word (tag : BitVec 32) (nonnegative : 0 ≤ tag.toInt) (bound : tag.toInt.toNat < 256) :
    Sail.shift_bits_right (Sail.shift_bits_left (sign_extend (m := 64) tag) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (Sail.BitVec.extractLsb (0x20#6) 5 0) = BitVec.ofNat 64 tag.toInt.toNat := by
  change ((sign_extend (m := 64) tag <<< (32 : Nat)) >>> (32 : Nat)) = _
  rw [nonnegative_word32 tag nonnegative]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  omega

/-- The common size/tag sum is the canonical initialized header. -/
theorem makeblock_header_word (count tag : Nat) :
    BitVec.ofNat 64 tag + BitVec.ofNat 64 (1024 * count) = blockHeader count tag := by
  unfold blockHeader
  rw [nat_shift_word, BitVec.add_comm]

end OCaml.Vm.Sim
