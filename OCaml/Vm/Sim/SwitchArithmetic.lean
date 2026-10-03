import OCaml.Vm.Sim.BranchCompare

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives
open LeanRV64DExecutable.Functions

/-- The tagged integer discriminator is always set. -/
theorem tag_low_bit (n : BitVec 63) : tag64 n &&& 1#64 = 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod, tag_toNat]
  omega

/-- A nonnegative represented integer is its ordinary native array index. -/
theorem longVal_nonnegative (n : BitVec 63) (positive : 0 ≤ n.toInt) :
    longVal n = BitVec.ofNat 64 n.toNat := by
  have msb : n.msb = false := by
    cases h : n.msb with
    | false => rfl
    | true => have := BitVec.toInt_neg_of_msb_true h; omega
  apply BitVec.eq_of_toNat_eq
  simp only [longVal, BitVec.toNat_signExtend, msb, Bool.false_eq_true,
    ↓reduceIte, Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- SWITCH scales its untagged integer selector by one bytecode word. -/
theorem switch_int_scale (n : BitVec 63) (positive : 0 ≤ n.toInt) :
    Sail.shift_bits_left
      (shift_bits_right_arith (tag64 n) (Sail.BitVec.extractLsb (0x01#6) 5 0))
      (Sail.BitVec.extractLsb (0x02#6) 5 0) = BitVec.ofNat 64 (4 * n.toNat) := by
  rw [longVal_native, longVal_nonnegative n positive]
  change (BitVec.ofNat 64 n.toNat <<< (2 : Nat)) = _
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n.toNat * BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

/-- The SWITCH table begins after the opcode and packed size operand. -/
theorem switch_table_word (pl : Place) (pc index : Nat) :
    (BitVec.ofNat 64 (pl.codeBase + 4 * pc) + 8#64) + BitVec.ofNat 64 (4 * index) =
      BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 2 + index)) := by
  rw [show (8#64) = BitVec.ofNat 64 (4 * 2) from rfl, codePc_add]
  simp only [Nat.mul_add, ← Nat.add_assoc, BitVec.ofNat_add]

end OCaml.Vm.Sim
