import OCaml.Vm.Sim.GrabAllocationArithmetic
import OCaml.Vm.Sim.NurseryInput
import OCaml.Vm.Sim.GrabRestore
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- GRAB reserves metadata, its old environment, and the saved arguments. -/
abbrev GrabNurseryInput (extra a domain limit : Nat) (c : Config) : Prop :=
  NurseryInput (extra + 4) a domain limit c

def grabReserveWrites : List Register :=
  [Register.x10, Register.x12, Register.x13, Register.x14, Register.x15, Register.x16,
   Register.x17, Register.x23] ++ noiseRegs

/-- The generated nursery reservation establishes all initializer inputs. -/
structure GrabReserved (before : Config) (extra a domain : Nat) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pc : pcOf after = some (0x800036c0#64)
  count : gpr after 10 = some (BitVec.ofNat 64 (extra + 4))
  header : gpr after 15 = some (BitVec.ofNat 64 (a - 8))
  bytes : gpr after 16 = some (BitVec.ofNat 64 (8 * (extra + 4)))
  savedExtra : gpr after 23 = some (BitVec.ofNat 64 extra)
  memory : after.σ.mem = writeLog before.σ.mem (grabReserveLog domain a)
  frame : StepFrameOut grabReserveWrites before.σ after.σ

end OCaml.Vm.Sim
