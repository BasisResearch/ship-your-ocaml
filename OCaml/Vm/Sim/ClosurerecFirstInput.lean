import OCaml.Vm.Sim.ClosurerecReady
import OCaml.Vm.Sim.ClosureArithmetic
import OCaml.Vm.Sim.ClosurerecArithmetic
import OCaml.Vm.Sim.OperandFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closurerecStackStart (sp count : Nat) : Nat := sp + 8 * (count - 1) - 8

def closurerecFirstLog (pl : Place) (sp functions count dest a : Nat) : List WEntry :=
  [(closurerecStackStart sp count, 8, BitVec.ofNat 64 a),
   (a, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest)),
   (a + 8, 8, BitVec.ofNat 64 (2 * (3 * functions - 1) + 1))]

/-- First-function stores and the preserved displacement word at the metadata cut. -/
structure ClosurerecFirstInput (c : Config) (pl : Place) (pc sp functions count dest a domain : Nat)
    (accu : BitVec 64) : Prop where
  captureRoom : 0 < count → 8 ≤ sp
  stackRoom : 8 ≤ sp + 8 * (count - 1)
  stackWrite : RamWriteAt (closurerecStackStart sp count) 8
  codeWrite : RamWriteAt a 8
  arityWrite : RamWriteAt (a + 8) 8
  image : ImageOutside (closurerecFirstLog pl sp functions count dest a)
  operandOutside : OutLRange (closurerecReadyLog c sp functions count a domain accu ++
    [(closurerecStackStart sp count, 8, BitVec.ofNat 64 a)]) (pl.codeBase + 4 * (pc + 3)) 4

def closurerecFirstWrites : List Register :=
  [Register.x8, Register.x9, Register.x10, Register.x11, Register.x12, Register.x13, Register.x14, Register.x15] ++ noiseRegs

def closurerecMetadataWrites : List Register :=
  [Register.x8, Register.x9, Register.x10, Register.x11, Register.x12, Register.x13, Register.x14,
   Register.x15, Register.x16, Register.x17, Register.x21, Register.x23, Register.x26, Register.x27] ++ noiseRegs

/-- Registers for the remaining infix headers, code pointers and closure stack. -/
structure ClosurerecInfixRegisters (pl : Place) (pc sp functions count a : Nat) (c : Config) : Prop where
  targetReg : gpr c 15 = some (BitVec.ofNat 64 (a + 24))
  codeReg : gpr c 8 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 4)))
  stackReg : gpr c 11 = some (BitVec.ofNat 64 (closurerecStackStart sp count))
  counter : gpr c 13 = some (3#64)
  limit : gpr c 10 = some (BitVec.ofNat 64 (3 * functions))
  arity : gpr c 12 = some (BitVec.ofNat 64 (2 * (3 * functions - 4) + 1))

/-- The first function is installed; multiple functions continue with infix metadata. -/
structure ClosurerecFirst (before : Config) (pl : Place) (pc sp functions count dest a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (if 1 < functions then 0x8000296c#64 else 0x800029b8#64)
  fields : ClosurerecFields pl pc sp functions count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  stackReg : gpr after 9 = some (BitVec.ofNat 64 (closurerecStackStart sp count))
  infixRegisters : 1 < functions → ClosurerecInfixRegisters pl pc sp functions count a after
  memory : after.σ.mem = writeLog before.σ.mem (closurerecReadyLog before sp functions count a domain accuWord ++
    closurerecFirstLog pl sp functions count dest a)
  frame : StepFrameOut closurerecMetadataWrites before.σ after.σ

end OCaml.Vm.Sim
