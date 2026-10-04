import OCaml.Vm.Sim.ClosurePrefixInput
import OCaml.Vm.Sim.NurseryArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The temporary capture push is disjoint from all scalar nursery observations. -/
abbrev ClosureNurseryInput (sp count a domain limit : Nat) (accu : BitVec 64) (c : Config) :=
  NurseryFrameInput (count + 2) a domain limit (closurePushLog sp count accu) c

theorem ClosureNurseryInput.after {pl : Place} {pc sp count a domain limit : Nat}
    {accu : BitVec 64} {c d : Config} (space : ClosureNurseryInput sp count a domain limit accu c)
    (front : ClosurePrefixed c pl pc sp count accu d) : NurseryInput (count + 2) a domain limit d :=
  space.transport front.memory

def closureReserveWrites : List Register :=
  [Register.x9, Register.x12, Register.x13, Register.x14, Register.x15] ++ noiseRegs

def closureReservationWrites : List Register :=
  [Register.x9, Register.x12, Register.x13, Register.x14, Register.x15,
   Register.x17, Register.x23, Register.x26, Register.x27] ++ noiseRegs

/-- The common nursery reservation preserves capture metadata and supplies the header. -/
structure ClosureReserved (before : Config) (pl : Place) (pc sp count a domain : Nat)
    (accu : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x80002a10#64)
  fields : ClosureFields pl pc sp count after
  header : gpr after 15 = some (BitVec.ofNat 64 (a - 8))
  memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu ++ grabReserveLog domain a)
  frame : StepFrameOut closureReservationWrites before.σ after.σ

end OCaml.Vm.Sim
