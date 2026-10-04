import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Primitives.ImageFrame
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- A tagged zero divisor selects the shared native exception setup. -/
structure DivisionZeroInput (sp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  stack : gpr c 9 = some sp
  read : ReadWindow sp 8
  zero : word c sp.toNat = 1#64

/-- Both integer division operations preserve memory before their shared zero path. -/
structure DivisionZeroPost (sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x80003c90#64
  stack : gpr after 9 = some sp
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut ([Register.x11] ++ noiseRegs) before.σ after.σ

end OCaml.Vm.Sim
