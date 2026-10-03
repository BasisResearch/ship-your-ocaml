import OCaml.Vm.Sim.ClosureNurseryInput
import OCaml.Vm.Sim.ClosureSnapshot

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closureHeaderLog (a count : Nat) : List WEntry :=
  [(a - 8, 8, blockHeader (count + 2) Bytecode.closureTag)]

def closureSetupLog (sp count a domain : Nat) (accu : BitVec 64) : List WEntry :=
  closurePushLog sp count accu ++ (grabReserveLog domain a ++ closureHeaderLog a count)

/-- Header initialization and capture-window geometry. The concrete snapshot
is proved from the actual push/setup log rather than assumed here. -/
structure ClosureInitInput (sp count a domain : Nat) (accu : BitVec 64) (c : Config) : Prop where
  headerImage : ImageOutside (closureHeaderLog a count)
  domainOutside : OutLRange (closureSetupLog sp count a domain accu) Layout.sym_Caml_state 8
  youngOutside : OutLRange (closureHeaderLog a count) (domain + Layout.off_young_ptr) 8
  reads : ∀ i, i < count → RamReadAt (closureSource sp count + 8 * i) 8
  writes : ∀ i, i < count → RamWriteAt (a + 16 + 8 * i) 8
  copyImage : ImageOutside (valueLog (a + 16) (closureWords c sp count accu))
  copySeparate : OutLRange (valueLog (a + 16) (closureWords c sp count accu)) (closureSource sp count) (8 * count)
  setupOutside : OutLRange (grabReserveLog domain a ++ closureHeaderLog a count) (closureSource sp count) (8 * count)

def closureInitWrites : List Register :=
  [Register.x10, Register.x11, Register.x13, Register.x14, Register.x15, Register.x16, Register.x21] ++ noiseRegs

def closureSetupWrites : List Register :=
  [Register.x9, Register.x10, Register.x11, Register.x12, Register.x13, Register.x14,
   Register.x15, Register.x16, Register.x17, Register.x21, Register.x23, Register.x26, Register.x27] ++ noiseRegs

structure ClosureCopyRegisters (sp count : Nat) (c : Config) : Prop where
  sourceReg : gpr c 13 = some (BitVec.ofNat 64 (closureSource sp count))
  counter : gpr c 15 = some (2#64)
  limit : gpr c 11 = some (BitVec.ofNat 64 (count + 2))

/-- Both native initializers establish the header and allocated pointer; only
nonempty captures need the index/cursor registers. -/
structure ClosureInitialized (before : Config) (pl : Place) (pc sp count a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (if 0 < count then 0x80002a44#64 else 0x80002a60#64)
  fields : ClosureFields pl pc sp count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  value : gpr after 10 = some (BitVec.ofNat 64 a)
  targetReg : gpr after 16 = some (BitVec.ofNat 64 a)
  copyRegisters : 0 < count → ClosureCopyRegisters sp count after
  memory : after.σ.mem = writeLog before.σ.mem (closureSetupLog sp count a domain accuWord)
  frame : StepFrameOut closureSetupWrites before.σ after.σ

theorem ClosureInitialized.copy_start {before after : Config} {pl : Place}
    {pc sp count a domain : Nat} {accu : BitVec 64}
    (front : ClosureInitialized before pl pc sp count a domain accu after) (positive : 0 < count) :
    ClosureCopyAt (closureSource sp count) a (closureWords before sp count accu) after 0 after := by
  have regs := front.copyRegisters positive
  refine ⟨front.good, front.tick, front.image, Nat.zero_le _, ?_, ?_, front.targetReg, ?_, ?_, rfl,
    (StepFrameOut.refl after.σ).widenChecked (allowed := closureCopyWrites) (by decide)⟩
  · simpa only [closure_words_length, positive, ite_true] using front.pcAt
  · simpa only [IndexedCopyShape.sourceWord, closureCopyShape, Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero] using regs.sourceReg
  · exact regs.counter
  · change gpr after 11 = some (BitVec.ofNat 64 ((closureWords before sp count accu).length + 2))
    rw [closure_words_length]; exact regs.limit

theorem ClosureInitInput.copy_after {before after : Config} {pl : Place}
    {pc sp count a domain : Nat} {accu : BitVec 64}
    (space : ClosureInitInput sp count a domain accu before) (room : 0 < count → 8 ≤ sp)
    (front : ClosureInitialized before pl pc sp count a domain accu after) :
    ClosureCopyRegion (closureSource sp count) a (closureWords before sp count accu) after := by
  refine ⟨?_, ?_, ?_, space.copyImage, ?_, ?_⟩
  · change (closureWords before sp count accu).length + 2 < 2^31
    rw [closure_words_length]; have small := front.fields.nurseryBound; omega
  · change ∀ i, i < (closureWords before sp count accu).length → RamReadAt (closureSource sp count + 8 * i) 8
    simpa only [closure_words_length] using space.reads
  · change ∀ i, i < (closureWords before sp count accu).length → RamWriteAt (a + 16 + 8 * i) 8
    simpa only [closure_words_length] using space.writes
  · change OutLRange (valueLog (a + 16) (closureWords before sp count accu)) (closureSource sp count)
      (8 * (closureWords before sp count accu).length)
    rw [closure_words_length]; exact space.copySeparate
  · intro i w selected
    exact closure_setup_snapshot room front.memory space.setupOutside selected

end OCaml.Vm.Sim
