import OCaml.Vm.Sim.ClosurerecPrefixInput
import OCaml.Vm.Sim.NurseryArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Recursive closures use the same prefix-framed nursery observations. -/
abbrev ClosurerecNurseryInput (sp functions count a domain limit : Nat) (accu : BitVec 64) (c : Config) :=
  NurseryFrameInput (closurerecSize functions count) a domain limit (closurePushLog sp count accu) c

theorem ClosurerecNurseryInput.after {pl : Place} {pc sp functions count a domain limit : Nat}
    {accu : BitVec 64} {c d : Config} (space : ClosurerecNurseryInput sp functions count a domain limit accu c)
    (front : ClosurerecPrefixed c pl pc sp functions count accu d) :
    NurseryInput (closurerecSize functions count) a domain limit d :=
  space.transport front.memory

def closurerecReserveWrites : List Register :=
  [Register.x9, Register.x11, Register.x13, Register.x14, Register.x15] ++ noiseRegs

def closurerecReservationWrites : List Register :=
  [Register.x9, Register.x10, Register.x11, Register.x13, Register.x14, Register.x15,
   Register.x16, Register.x17, Register.x23, Register.x26, Register.x27] ++ noiseRegs

/-- The recursive reservation preserves size and metadata and supplies the header. -/
structure ClosurerecReserved (before : Config) (pl : Place) (pc sp functions count a domain : Nat)
    (accu : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x800028cc#64)
  fields : ClosurerecFields pl pc sp functions count after
  sizeReg : gpr after 10 = some (BitVec.ofNat 64 (closurerecSize functions count))
  header : gpr after 15 = some (BitVec.ofNat 64 (a - 8))
  memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu ++ grabReserveLog domain a)
  frame : StepFrameOut closurerecReservationWrites before.σ after.σ

end OCaml.Vm.Sim
