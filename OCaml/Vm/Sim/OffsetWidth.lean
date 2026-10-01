import OCaml.Vm.Sim.OffsetintSegment
import OCaml.Vm.Sim.OffsetintPins
import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode LeanRV64DExecutable.Functions

/-- The exact operand contribution in `tr_offsetint`'s postcondition:
LW sign-extension, SLLIW on the low 32 bits, then sign-extension to XLEN. -/
def offsetintOperand (w : BitVec 32) : BitVec 64 :=
  sign_extend (m := 64) (Sail.shift_bits_left
    (Sail.BitVec.extractLsb (sign_extend (m := 64) w) 31 0) (0x01#5))

theorem offsetintOperand_large :
    offsetintOperand (0x40000000#32) = BitVec.ofInt 64 (-2147483648) := by decide

/-- A checked arithmetic obstruction to the 64-bit-shift model of
OFFSETINT. Kept independent of `stepI` so a corrected semantics can retain
the regression witness. This is not a complete Loaded/run counterexample. -/
theorem offsetint_width_obstruction :
    untag (tag64 64 + offsetintOperand (0x40000000#32)) ≠
      untag (tag64 64 + (BitVec.ofInt 64 1073741824 <<< (1 : Nat))) := by decide

end OCaml.Vm.Sim
