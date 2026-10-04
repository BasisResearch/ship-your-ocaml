import OCaml.Vm.Sim.DivisionZeroState
import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def divisionZeroEnvSp (sp : BitVec 64) : BitVec 64 := sp - 8#64

def divisionZeroExtern (domain : BitVec 64) : BitVec 64 := domain + BitVec.ofNat 64 Layout.off_extern_sp

def divisionZeroStackLog (code sp env : BitVec 64) : List WEntry :=
  [(sp.toNat, 8, code + 8#64), ((divisionZeroEnvSp sp).toNat, 8, env)]

def divisionZeroSetupLog (code sp env domain : BitVec 64) : List WEntry :=
  divisionZeroStackLog code sp env ++ [((divisionZeroExtern domain).toNat, 8, divisionZeroEnvSp sp)]

/-- The common zero-divisor path publishes the native C-call stack frame. -/
structure DivisionZeroSetupInput (code sp env domain : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  codeReg : gpr c 8 = some code
  stack : gpr c 9 = some sp
  environment : gpr c 25 = some env
  domainWord : word c Layout.sym_Caml_state = domain
  codeWrite : WriteWindow sp 8
  envWrite : WriteWindow (divisionZeroEnvSp sp) 8
  externWrite : WriteWindow (divisionZeroExtern domain) 8
  domainOutside : OutLRange (divisionZeroStackLog code sp env) Layout.sym_Caml_state 8
  imageOutside : ImageOutside (divisionZeroSetupLog code sp env domain)

/-- The actual JAL reaches the zero-divisor callee with its native return address set. -/
structure DivisionZeroSetupPost (code sp env domain : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x8000d1d4#64
  returnReg : gpr after 1 = some 0x80003cb0#64
  stack : gpr after 9 = some (divisionZeroEnvSp sp)
  memory : after.σ.mem = writeLog before.σ.mem (divisionZeroSetupLog code sp env domain)
  frame : StepFrameOut ([Register.x1, Register.x8, Register.x9, Register.x15] ++ noiseRegs) before.σ after.σ

end OCaml.Vm.Sim
