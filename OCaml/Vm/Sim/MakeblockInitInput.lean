import OCaml.Vm.Sim.MakeblockReserved
import OCaml.Vm.Sim.MakeblockLog

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Source window and setup separation supplied by the nursery/stack invariant. -/
structure MakeblockInitInput (sp count tag a domain : Nat) (accu : BitVec 64) (c : Config) : Prop where
  copy : CursorCopyRegion sp (a + 8) (stackWords c sp (count - 1)) c
  sourceOutside : OutLRange (makeblockSetupLog domain a count tag accu) sp (8 * (count - 1))

def makeblockInitWrites : List Register :=
  [Register.x8, Register.x10, Register.x11, Register.x12, Register.x13,
   Register.x14, Register.x15] ++ noiseRegs

def makeblockSetupWrites : List Register :=
  [Register.x8, Register.x10, Register.x11, Register.x12, Register.x13,
   Register.x14, Register.x15, Register.x16, Register.x23, Register.x26] ++ noiseRegs

/-- Registers used only by the multi-field constructor's copy and suffix. -/
structure MakeblockCopyRegisters (sp count a : Nat) (c : Config) : Prop where
  sourceReg : gpr c 15 = some (BitVec.ofNat 64 sp)
  targetReg : gpr c 14 = some (BitVec.ofNat 64 (a + 8))
  limit : gpr c 12 = some (BitVec.ofNat 64 (sp + 8 * (count - 1)))
  bytes : gpr c 10 = some (BitVec.ofNat 64 (8 * (count - 1)))

/-- Both generated initializer branches establish the same initialized block
prefix. Only the multi-field branch needs copy registers. -/
structure MakeblockInitialized (before : Config) (pl : Place) (pc sp count tag a domain : Nat)
    (accu : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (if 1 < count then 0x800026cc#64 else 0x80003c74#64)
  header : gpr after 11 = some (BitVec.ofNat 64 (a - 8))
  stack : gpr after 9 = some (BitVec.ofNat 64 sp)
  nextCode : gpr after 26 = some (BitVec.ofNat 64 (pl.codeBase + 4 * (pc + 3)))
  copyRegisters : 1 < count → MakeblockCopyRegisters sp count a after
  memory : after.σ.mem = writeLog before.σ.mem (makeblockSetupLog domain a count tag accu)
  frame : StepFrameOut makeblockSetupWrites before.σ after.σ

theorem MakeblockInitialized.copy_start {before after : Config} {pl : Place}
    {pc sp count tag a domain : Nat} {accu : BitVec 64}
    (front : MakeblockInitialized before pl pc sp count tag a domain accu after)
    (more : 1 < count) :
    MakeblockCopyAt sp (a + 8) (stackWords before sp (count - 1)) after 0 after := by
  have regs := front.copyRegisters more
  refine ⟨front.good, front.tick, front.image, by omega, ?_, ?_, ?_, ?_, ?_, (StepFrameOut.refl after.σ).widenChecked (allowed := cursorCopyWrites) (by decide)⟩
  · simpa only [stackWords, List.length_map, List.length_range,
      show 0 < count - 1 by omega, more, ite_true] using front.pcAt
  · simpa only [cursorCopyShape, PointerCopyShape.sourceWord, Bool.false_eq_true,
      ite_false, Nat.mul_zero, Nat.add_zero] using regs.sourceReg
  · simpa only [Nat.mul_zero, Nat.add_zero] using regs.targetReg
  · simpa only [cursorCopyShape, PointerCopyShape.counterBase, Bool.false_eq_true,
      ite_false, stackWords, List.length_map, List.length_range] using regs.limit
  · rfl

theorem MakeblockInitInput.copy_after {before after : Config} {pl : Place}
    {pc sp count tag a domain : Nat} {accu : BitVec 64}
    (space : MakeblockInitInput sp count tag a domain accu before)
    (front : MakeblockInitialized before pl pc sp count tag a domain accu after) :
    CursorCopyRegion sp (a + 8) (stackWords before sp (count - 1)) after := by
  apply space.copy.frame _ front.memory
  simpa only [stackWords, List.length_map, List.length_range] using space.sourceOutside

end OCaml.Vm.Sim
