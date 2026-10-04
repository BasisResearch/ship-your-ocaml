import OCaml.Vm.Sim.ClosurerecNurseryInput
import OCaml.Vm.Sim.ClosurerecCopy
import OCaml.Vm.Sim.ClosureSnapshot

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def closurerecCaptureBase (a functions : Nat) : Nat := a + 8 * (3 * functions - 1)

def closurerecHeaderLog (a functions count : Nat) : List WEntry :=
  [(a - 8, 8, blockHeader (closurerecSize functions count) Bytecode.closureTag)]

def closurerecSetupLog (sp functions count a domain : Nat) (accu : BitVec 64) : List WEntry :=
  closurePushLog sp count accu ++ (grabReserveLog domain a ++ closurerecHeaderLog a functions count)

/-- Header initialization and recursive capture geometry; the concrete source
snapshot follows from the actual prefix and its disjoint setup stores. -/
structure ClosurerecInitInput (sp functions count a domain : Nat) (accu : BitVec 64) (c : Config) : Prop where
  headerImage : ImageOutside (closurerecHeaderLog a functions count)
  domainOutside : OutLRange (closurerecSetupLog sp functions count a domain accu) Layout.sym_Caml_state 8
  youngOutside : OutLRange (closurerecHeaderLog a functions count) (domain + Layout.off_young_ptr) 8
  upper : closurerecCaptureBase a functions + 8 * count < 2^64
  reads : ∀ i, i < count → RamReadAt (closureSource sp count + 8 * i) 8
  writes : ∀ i, i < count → RamWriteAt (closurerecCaptureBase a functions + 8 * i) 8
  copyImage : ImageOutside (valueLog (closurerecCaptureBase a functions) (closureWords c sp count accu))
  copySeparate : OutLRange (valueLog (closurerecCaptureBase a functions) (closureWords c sp count accu)) (closureSource sp count) (8 * count)
  setupOutside : OutLRange (grabReserveLog domain a ++ closurerecHeaderLog a functions count) (closureSource sp count) (8 * count)

def closurerecInitWrites : List Register :=
  [Register.x10, Register.x11, Register.x14, Register.x15, Register.x21] ++ noiseRegs

def closurerecSetupWrites : List Register :=
  [Register.x9, Register.x10, Register.x11, Register.x13, Register.x14,
   Register.x15, Register.x16, Register.x17, Register.x21, Register.x23, Register.x26, Register.x27] ++ noiseRegs

structure ClosurerecCopyRegisters (a functions count : Nat) (c : Config) : Prop where
  base : gpr c 10 = some (BitVec.ofNat 64 (closurerecCaptureBase a functions))
  cursor : gpr c 14 = some (BitVec.ofNat 64 (closurerecCaptureBase a functions))
  limit : gpr c 11 = some (BitVec.ofNat 64 (closurerecCaptureBase a functions + 8 * count))

/-- Both recursive initializers establish the header and allocated pointer;
nonempty captures additionally establish the destination-displacement loop. -/
structure ClosurerecInitialized (before : Config) (pl : Place) (pc sp functions count a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  image : ExecutableImage after
  pcAt : pcOf after = some (if 0 < count then 0x80002904#64 else 0x8000291c#64)
  fields : ClosurerecFields pl pc sp functions count after
  accu : gpr after 21 = some (BitVec.ofNat 64 a)
  value : gpr after 15 = some (BitVec.ofNat 64 a)
  copyRegisters : 0 < count → ClosurerecCopyRegisters a functions count after
  memory : after.σ.mem = writeLog before.σ.mem (closurerecSetupLog sp functions count a domain accuWord)
  frame : StepFrameOut closurerecSetupWrites before.σ after.σ

theorem ClosurerecInitialized.copy_start {before after : Config} {pl : Place}
    {pc sp functions count a domain : Nat} {accu : BitVec 64}
    (front : ClosurerecInitialized before pl pc sp functions count a domain accu after) (positive : 0 < count) :
    ClosurerecCopyAt (closureSource sp count) (closurerecCaptureBase a functions)
      (closureWords before sp count accu) after 0 after := by
  have regs := front.copyRegisters positive
  refine ⟨front.good, front.tick, front.image, Nat.zero_le _, ?_, front.fields.sourceReg, ?_, ?_, rfl,
    (StepFrameOut.refl after.σ).widenChecked (allowed := closurerecCopyWrites) (by decide)⟩
  · simpa only [closure_words_length, positive, ite_true] using front.pcAt
  · simpa only [Nat.mul_zero, Nat.add_zero] using regs.cursor
  · change gpr after 11 = some (BitVec.ofNat 64 (closurerecCaptureBase a functions + 8 * (closureWords before sp count accu).length))
    rw [closure_words_length]; exact regs.limit

theorem ClosurerecInitInput.copy_after {before after : Config} {pl : Place}
    {pc sp functions count a domain : Nat} {accu : BitVec 64}
    (space : ClosurerecInitInput sp functions count a domain accu before) (room : 0 < count → 8 ≤ sp)
    (front : ClosurerecInitialized before pl pc sp functions count a domain accu after) :
    ClosurerecCopyRegion (closureSource sp count) (closurerecCaptureBase a functions)
      (closureWords before sp count accu) after := by
  refine ⟨?_, ?_, ?_, space.copyImage, ?_, ?_⟩
  · change closurerecCaptureBase a functions + 8 * (closureWords before sp count accu).length < 2^64
    rw [closure_words_length]; exact space.upper
  · simpa only [closure_words_length] using space.reads
  · simpa only [closure_words_length] using space.writes
  · simpa only [closure_words_length] using space.copySeparate
  · intro i w selected
    exact closure_setup_snapshot room front.memory space.setupOutside selected

end OCaml.Vm.Sim
