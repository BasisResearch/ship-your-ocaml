import OCaml.Vm.Sim.ClosurePrefixInput
import OCaml.Vm.Sim.FramePins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closurerecSize (functions count : Nat) : Nat := 3 * functions - 1 + count

def closurerecPrefixWrites : List Register :=
  [Register.x10, Register.x15, Register.x16, Register.x17, Register.x23, Register.x26, Register.x27] ++ noiseRegs

def closurerecFieldRegisters : List Register :=
  [Register.x17, Register.x26, Register.x27, Register.x16, Register.x23]

/-- Persistent recursive-closure metadata, distinct from allocator temporaries. -/
structure ClosurerecFields (pl : Place) (pc sp functions count : Nat) (c : Config) : Prop where
  positive : 0 < functions
  nurseryBound : closurerecSize functions count ≤ 256
  functionsReg : gpr c 17 = some (BitVec.ofNat 64 functions)
  countReg : gpr c 26 = some (BitVec.ofNat 64 count)
  environmentOffset : gpr c 27 = some (BitVec.ofNat 64 (3 * functions - 1))
  codeBase : gpr c 16 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3)))
  sourceReg : gpr c 23 = some (BitVec.ofNat 64 (closureSource sp count))

/-- One frame certificate preserves the whole named metadata bundle. -/
theorem ClosurerecFields.frame {pl : Place} {pc sp functions count : Nat} {before after : Config}
    {written : List Register} (fields : ClosurerecFields pl pc sp functions count before)
    (frame : StepFrameOut written before.σ after.σ)
    (avoid : ∀ r ∈ closurerecFieldRegisters, ∀ w ∈ written, (w == r) = false) :
    ClosurerecFields pl pc sp functions count after := by
  have pins : PinsHold before.σ
      [⟨Register.x17, BitVec.ofNat 64 functions⟩, ⟨Register.x26, BitVec.ofNat 64 count⟩,
       ⟨Register.x27, BitVec.ofNat 64 (3 * functions - 1)⟩,
       ⟨Register.x16, BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3))⟩,
       ⟨Register.x23, BitVec.ofNat 64 (closureSource sp count)⟩] :=
    ⟨fields.functionsReg, fields.countReg, fields.environmentOffset, fields.codeBase, fields.sourceReg, trivial⟩
  obtain ⟨functionsReg, countReg, environmentOffset, codeBase, sourceReg, _⟩ := frame_pins frame pins avoid
  exact ⟨fields.positive, fields.nurseryBound, functionsReg, countReg, environmentOffset, codeBase, sourceReg⟩

/-- Both native capture paths reach the common recursive-closure reservation. -/
structure ClosurerecPrefixed (before : Config) (pl : Place) (pc sp functions count : Nat)
    (accu : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (0x8000289c#64)
  fields : ClosurerecFields pl pc sp functions count after
  sizeReg : gpr after 10 = some (BitVec.ofNat 64 (closurerecSize functions count))
  memory : after.σ.mem = writeLog before.σ.mem (closurePushLog sp count accu)
  frame : StepFrameOut closurerecPrefixWrites before.σ after.σ

end OCaml.Vm.Sim
