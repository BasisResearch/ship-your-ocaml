import OCaml.Vm.Sim.GrabAllocationArithmetic
import OCaml.Vm.Sim.GrabRestore
import OCaml.Vm.Sim.WriteGeometry
import OCaml.Vm.Sim.StackStore
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def grabReserveLog (domain a : Nat) : List WEntry :=
  [(domain + Layout.off_young_ptr, 8, BitVec.ofNat 64 (a - 8))]

/-- Scalar G1 nursery observations. These are memory and capacity conditions,
not an assumption about the allocating arm's execution. -/
structure GrabNurseryInput (extra a domain limit : Nat) (c : Config) : Prop where
  small : extra + 4 < 2^31
  room : 8 ≤ a
  domainValue : word c Layout.sym_Caml_state = BitVec.ofNat 64 domain
  youngValue : word c (domain + Layout.off_young_ptr) = BitVec.ofNat 64 (a + 8 * (extra + 4))
  limitValue : word c (domain + Layout.off_young_limit) = BitVec.ofNat 64 limit
  youngWrite : RamWriteAt (domain + Layout.off_young_ptr) 8
  limitRead : RamReadAt (domain + Layout.off_young_limit) 8
  headerWrite : RamWriteAt (a - 8) 8
  capacity : limit ≤ a - 8
  image : ImageOutside (grabReserveLog domain a)

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
