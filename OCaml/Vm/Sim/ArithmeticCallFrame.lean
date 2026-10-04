import OCaml.Vm.Sim.StackConsume

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Caller observations retained while a binary libgcc function runs. -/
structure ArithmeticCallFrame (before : Config) (pl : Place) (pc sp : Nat) (c : Config) : Prop where
  nextCode : gpr c 23 = some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  stack : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  memory : c.σ.mem = before.σ.mem
  output : c.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ consumePreserved, c.σ.regs.get? r = before.σ.regs.get? r

end OCaml.Vm.Sim
