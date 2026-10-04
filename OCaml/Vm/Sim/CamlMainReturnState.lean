import OCaml.Vm.Sim.InterpReturnState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

abbrev CamlMainSavedFrame := NativeSavedFrame Layout.camlMainSavedRegs Layout.camlMainSaveOffset

/-- caml_main checks the interpreter result before restoring its saved ABI frame. -/
structure CamlMainReturnInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x80004ff8#64)
  tick : c.tick < 2
  frame : CamlMainSavedFrame nativeSp saved c
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  ordinary : value &&& 3#64 ≠ 2#64
  value : gpr c 10 = some value
  aligned : (saved 1).toNat % 4 = 0

def camlMainReturnWrites : List Register :=
  Layout.camlMainSavedRegs.map gprReg ++ [Register.x2, Register.x14, Register.x15] ++ noiseRegs

/-- The normal caml_main return retains the result, memory and console output. -/
structure CamlMainReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  stack : gpr after 2 = some (BitVec.ofNat 64 (nativeSp + Layout.camlMainFrameBytes))
  value : gpr after 10 = some value
  registers : ∀ r ∈ Layout.camlMainSavedRegs, gpr after r = some (saved r)
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut camlMainReturnWrites before.σ after.σ

end OCaml.Vm.Sim
