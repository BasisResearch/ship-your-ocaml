import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Bytecode operand reads survive any exact write log disjoint from their four bytes. -/
theorem OperandAt.read32_mem_log {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32}
    {before : Config} {after : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry}
    (operand : OperandAt P pl i w) (repr : CodeRepr P.code pl.codeBase before)
    (outside : OutLRange log (pl.codeBase + 4 * i) 4)
    (memory : after = writeLog before.σ.mem log) :
    bytesT4 after (pl.codeBase + 4 * i) = w := by
  rw [← bytesT_four_eq, memory, bytesT_writeLog_out _ outside]
  exact code_read repr operand.fetch

/-- Configuration-level wrapper for represented arm boundaries. -/
theorem OperandAt.read32_log {P : Prog} {pl : Place} {i : Nat} {w : BitVec 32}
    {before after : Config} {log : List WEntry}
    (operand : OperandAt P pl i w) (repr : CodeRepr P.code pl.codeBase before)
    (outside : OutLRange log (pl.codeBase + 4 * i) 4)
    (memory : after.σ.mem = writeLog before.σ.mem log) :
    bytesT4 after.σ.mem (pl.codeBase + 4 * i) = w :=
  operand.read32_mem_log repr outside memory

end OCaml.Vm.Sim
