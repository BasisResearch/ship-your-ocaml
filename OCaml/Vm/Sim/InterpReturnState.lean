import OCaml.Vm.Sim.ReadOnly
import OCaml.Vm.Sim.LogRead
import Vsa.Sim.FrameWriteSet
import Vsa.Sim.Muldi3Spec

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Callee-saved native registers at the offsets extracted from the prologue. -/
structure InterpSavedFrame (nativeSp : Nat) (saved : Nat → BitVec 64) (c : Config) : Prop where
  words : ∀ r ∈ Layout.interpSavedRegs, word c (nativeSp + Layout.interpSaveOffset r) = saved r
  reads : ∀ r ∈ Layout.interpSavedRegs, RamReadAt (nativeSp + Layout.interpSaveOffset r) 8

/-- Runtime stores outside the saved native frame retain every return value. -/
theorem InterpSavedFrame.frame {nativeSp : Nat} {saved : Nat → BitVec 64} {c after : Config} {log : List WEntry}
    (h : InterpSavedFrame nativeSp saved c)
    (outside : ∀ r ∈ Layout.interpSavedRegs, OutLRange log (nativeSp + Layout.interpSaveOffset r) 8)
    (memory : after.σ.mem = writeLog c.σ.mem log) : InterpSavedFrame nativeSp saved after := by
  refine ⟨?_, h.reads⟩
  intro r hr
  have same : word after (nativeSp + Layout.interpSaveOffset r) = word c (nativeSp + Layout.interpSaveOffset r) := by
    rw [word, memory]
    exact bytesT_writeLog_out c.σ.mem (outside r hr)
  exact same.trans (h.words r hr)

/-- Entry to the shared interpreter epilogue after STOP or an uncaught return. -/
structure InterpReturnInput (nativeSp : Nat) (saved : Nat → BitVec 64) (value : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  pc : pcOf c = some (0x8000331c#64)
  tick : c.tick < 2
  frame : InterpSavedFrame nativeSp saved c
  stack : gpr c 2 = some (BitVec.ofNat 64 nativeSp)
  value : gpr c Layout.reg_accu = some value
  aligned : (saved 1).toNat % 4 = 0

def interpReturnWrites : List Register :=
  (Layout.interpSavedRegs.map gprReg) ++ [Register.x2, Register.x10] ++ noiseRegs

/-- Return restores the complete native ABI frame, result and caller stack. -/
structure InterpReturnPost (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  stack : gpr after 2 = some (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes))
  value : gpr after 10 = some value
  registers : ∀ r ∈ Layout.interpSavedRegs, gpr after r = some (saved r)
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut interpReturnWrites before.σ after.σ

end OCaml.Vm.Sim
