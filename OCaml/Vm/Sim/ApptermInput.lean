import OCaml.Vm.Sim.BackwardCopy
import OCaml.Vm.Sim.ApptermArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Generic APPTERM uses the same restoration contract with a backward write log.
The represented loop invariant supplies these geometry/separation facts. -/
structure ApptermWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high count slots : Nat) : Prop
    extends TailcallMemoryOk P s c pl cp sp high count slots
      (reverseCopyLog (tailcallStart sp count slots) (stackWords c sp count) 0) where
  copy : BackwardCopyRegion sp (tailcallStart sp count slots) (stackWords c sp count) c
  enter : EnterOutside (reverseCopyLog (tailcallStart sp count slots) (stackWords c sp count) 0) c

def apptermSetupWrites : List Register :=
  [Register.x9, Register.x10, Register.x11, Register.x12, Register.x14, Register.x15, Register.x23] ++ noiseRegs

/-- The prefix prepares the complete counted-copy entry plus its two suffix inputs. -/
structure ApptermCopyStart (before : Config) (sp count slots : Nat) (after : Config) : Prop where
  copy : BackwardCopyAt sp (tailcallStart sp count slots) (stackWords before sp count) after
    (stackWords before sp count).length after
  extraCount : gpr after 10 = some (BitVec.ofNat 64 (count - 1))
  base : gpr after 11 = some (BitVec.ofNat 64 (tailcallStart sp count slots))
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut apptermSetupWrites before.σ after.σ

/-- Memory-preserving prefix execution transports the original copy snapshot. -/
theorem ApptermWriteOk.copy_after {P : Prog} {s : St} {c after : Config} {pl : Place} {cp : ChanPlace}
    {sp high count slots : Nat} (space : ApptermWriteOk P s c pl cp sp high count slots)
    (front : ApptermCopyStart c sp count slots after) :
    BackwardCopyRegion sp (tailcallStart sp count slots) (stackWords c sp count) after := by
  refine ⟨space.copy.room, space.copy.direction, space.copy.small, space.copy.sourceUpper,
    space.copy.targetUpper, space.copy.reads, space.copy.writes, space.copy.image, ?_⟩
  intro i w selected
  simpa only [word, front.memory] using space.copy.snapshot i w selected

end OCaml.Vm.Sim
