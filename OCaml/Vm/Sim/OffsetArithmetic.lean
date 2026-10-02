import OCaml.Vm.Sim.OffsetWidth
import OCaml.Vm.Sim.BinaryArithmetic
import Init.Data.BitVec.Bitblast

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode OCaml.Vm.Primitives LeanRV64DExecutable.Functions

/-- SLLIW discards LW's upper sign bits before shifting the 32-bit operand. -/
theorem offsetintOperand_eq (w : BitVec 32) :
    offsetintOperand w = (w <<< (1 : Nat)).signExtend 64 := by
  have low : Sail.BitVec.extractLsb (sign_extend (m := 64) w) 31 0 = w := by
    change (w.signExtend 64).extractLsb' 0 32 = w
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, BitVec.getLsbD_signExtend,
      hi, show i < 64 by omega, decide_true, Bool.true_and, ite_true]
  simp only [offsetintOperand, low]
  rfl

/-- The corrected width-preserving operand contribution is even, so adding
it to a tagged integer needs no additional tag adjustment. -/
theorem tag_offsetint (a : BitVec 63) (w : BitVec 32) :
    tag64 (untag (tag64 a + offsetintOperand w)) = tag64 a + offsetintOperand w := by
  apply tag_untag_odd
  rw [offsetintOperand_eq, BitVec.getLsbD_add (by decide)]
  have tagOdd : (tag64 a).getLsbD 0 = true := by simp [tag64]
  have offsetEven : ((w <<< (1 : Nat)).signExtend 64).getLsbD 0 = false := by
    rw [BitVec.getLsbD_signExtend]
    simp
  simp only [tagOdd, offsetEven, BitVec.carry_zero, Bool.xor_false]

/-- Native operand contribution equals the corrected stepI expression. -/
theorem offsetintOperand_model (w : BitVec 32) :
    offsetintOperand w = ((BitVec.ofInt 32 w.toInt <<< (1 : Nat)).signExtend 64) := by
  rw [BitVec.ofInt_toInt, offsetintOperand_eq]

end OCaml.Vm.Sim
