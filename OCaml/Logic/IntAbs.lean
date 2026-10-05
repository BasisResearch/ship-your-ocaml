import OCaml.Logic.Function
import OCaml.Vm.Sim.ImmediateArithmetic

namespace OCaml.Bytecode

/-- Signed machine-integer absolute value, including OCaml's modular
minimum-integer overflow behavior. -/
def absWord (n : BitVec 63) : BitVec 63 := if n.toInt < 0 then -n else n

/-- The compiled signed branch tests precisely negativity of the OCaml int. -/
theorem abs_branch (n : BitVec 63) :
    (longVal n).slt 0 = decide (n.toInt < 0) := by
  simp [longVal, BitVec.slt, BitVec.toInt_signExtend_of_le]

end OCaml.Bytecode
