import Vsa.Sim.FrameWriteSet
import OCaml.Vm.Sim.NativeSavedFrame
import OCaml.Vm.Primitives.Control
import OCaml.Vm.Sim.ComparisonArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- The shared saved-frame relation instantiated at the checked jmp_buf offsets. -/
abbrev JumpSavedFrame := NativeSavedFrame Layout.jumpSavedRegs Layout.jumpSaveOffset

/-- longjmp returns the requested value, replacing zero by one as required by C. -/
def longjmpValue (value : BitVec 64) : BitVec 64 := if value = 0#64 then 1#64 else value

/-- seqz followed by add implements longjmp's zero-to-one rule for every word. -/
theorem longjmp_compare_value (value : BitVec 64) :
    compareValue true value 1#64 + value = longjmpValue value := by
  by_cases zero : value = 0#64
  · subst value; rfl
  · have positive : 0 < value.toNat := by
      have nonzero : value.toNat ≠ 0 := by
        intro eq
        apply zero
        apply BitVec.eq_of_toNat_eq
        simpa using eq
      omega
    have guard : zopz0zI_u value 1#64 = false := by
      rw [native_ult, BitVec.ule_eq_not_ult, Bool.not_not]
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_false_iff_not]
      omega
    simp only [compareValue, ite_true, guard, longjmpValue, if_neg zero]
    exact BitVec.zero_add value

/-- Native restoration reads a valid environment and uses its saved return target. -/
structure LongjmpInput (buffer : Nat) (saved : Nat → BitVec 64) (value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  frame : JumpSavedFrame buffer saved c
  bufferReg : gpr c 10 = some (BitVec.ofNat 64 buffer)
  valueReg : gpr c 11 = some value
  aligned : (saved 1).toNat % 4 = 0

def longjmpWrites : List Register := Layout.jumpSavedRegs.map gprReg ++ [Register.x10] ++ noiseRegs

/-- Nonlocal return restores all saved registers including the saved native stack. -/
structure LongjmpPost (before : Config) (saved : Nat → BitVec 64) (value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  registers : ∀ r ∈ Layout.jumpSavedRegs, gpr after r = some (saved r)
  value : gpr after 10 = some (longjmpValue value)
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut longjmpWrites before.σ after.σ

end OCaml.Vm.Sim
