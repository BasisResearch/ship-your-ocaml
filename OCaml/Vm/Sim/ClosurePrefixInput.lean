import OCaml.Vm.Sim.ClosureRestore
import OCaml.Vm.Sim.WriteGeometry
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closureSource (sp count : Nat) : Nat := if 0 < count then sp - 8 else sp

/-- Only a nonempty closure needs the temporary accumulator stack slot. -/
structure ClosurePushInput (sp count : Nat) (accu : BitVec 64) : Prop where
  room : 0 < count → 8 ≤ sp
  write : 0 < count → RamWriteAt (sp - 8) 8
  image : ImageOutside (closurePushLog sp count accu)

def closurePrefixWrites : List Register :=
  [Register.x15, Register.x17, Register.x23, Register.x26, Register.x27] ++ noiseRegs

def closureFieldRegisters : List Register := [Register.x17, Register.x23, Register.x26, Register.x27]

/-- Persistent native closure metadata, shared by prefix, reservation and initialization. -/
structure ClosureFields (pl : Place) (pc sp count : Nat) (c : Config) : Prop where
  nurseryBound : count ≤ 254
  countReg : gpr c 17 = some (BitVec.ofNat 64 count)
  fieldCount : gpr c 26 = some (BitVec.ofNat 64 (count + 2))
  codeBase : gpr c 27 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 2)))
  sourceReg : gpr c 23 = some (BitVec.ofNat 64 (closureSource sp count))

/-- A generated frame preserves closure metadata with one finite register check. -/
theorem ClosureFields.frame {pl : Place} {pc sp count : Nat} {before after : Config} {written : List Register}
    (fields : ClosureFields pl pc sp count before) (frame : StepFrameOut written before.σ after.σ)
    (avoid : ∀ r ∈ closureFieldRegisters, ∀ w ∈ written, (w == r) = false) :
    ClosureFields pl pc sp count after :=
  ⟨fields.nurseryBound,
    (frame.frame Register.x17 (avoid _ (by decide))).trans fields.countReg,
    (frame.frame Register.x26 (avoid _ (by decide))).trans fields.fieldCount,
    (frame.frame Register.x27 (avoid _ (by decide))).trans fields.codeBase,
    (frame.frame Register.x23 (avoid _ (by decide))).trans fields.sourceReg⟩

/-- Both native prefixes decode the count and establish the original capture
source, allocation size and code-offset base for the common reservation. -/
structure ClosurePrefixed (before : Config) (pl : Place) (pc sp count : Nat)
    (accu : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x800029e8#64)
  fields : ClosureFields pl pc sp count after
  memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu)
  frame : StepFrameOut closurePrefixWrites before.σ after.σ

end OCaml.Vm.Sim
