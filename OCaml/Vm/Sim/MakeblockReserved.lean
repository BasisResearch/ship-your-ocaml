import OCaml.Vm.Sim.MakeblockInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

def makeblockReserveWrites : List Register :=
  [Register.x8, Register.x11, Register.x12, Register.x13, Register.x14,
   Register.x15, Register.x16, Register.x23, Register.x26] ++ noiseRegs

/-- The generic constructor has decoded both operands and reserved its nursery block. -/
structure MakeblockReserved (before : Config) (pl : Place) (pc count a domain : Nat)
    (tag : BitVec 32) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x80002688#64)
  countReg : gpr after 23 = some (BitVec.ofNat 64 count)
  tagReg : gpr after 8 = some (LeanRV64DExecutable.Functions.sign_extend (m := 64) tag)
  header : gpr after 14 = some (BitVec.ofNat 64 (a - 8))
  nextCode : gpr after 26 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3)))
  memory : after.σ.mem = writeLog before.σ.mem (grabReserveLog domain a)
  frame : StepFrameOut makeblockReserveWrites before.σ after.σ

end OCaml.Vm.Sim
