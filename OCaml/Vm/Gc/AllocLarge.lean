import OCaml.Vm.Gc.AllocFinish
import OCaml.Vm.Gc.BestFitLargeFootprint

namespace OCaml.Vm.Gc.AllocLarge
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Free-list call registers supplied by the wrapper's decoded JALR. -/
def freeRegs (sp size : BitVec 64) (n : Nat) :=
  if n = 1 then AllocEntry.returnPc else if n = 2 then sp else size

def resultHeader (sp size : BitVec 64) (c : Config) := BestFitFallback.largeHeader (freeRegs sp size) c
def freeEffect (sp size : BitVec 64) (c : Config) := BestFitFallback.completeEffect (freeRegs sp size) c
def allocated (sp size : BitVec 64) (c : Config) := AllocFinish.snapshot (freeEffect sp size c) c

def effect (sp size : BitVec 64) (c : Config) :=
  AllocFinish.effect sp size (resultHeader sp size c) (freeEffect sp size c) c

/-- Large-block alternative and successful wrapper-continuation conditions.
All later memory observations refer to explicit initial write-log snapshots. -/
structure Conditions (sp size : BitVec 64) (c : Config) : Prop
    extends BestFitFallback.MissingConditions (freeRegs sp size) c where
  tagRead : ReadWindow (sp + BitVec.ofNat 64 AllocEntry.tagOffset) 8
  emptyBitmap : BestFitFallback.filtered size (BestFitFallback.bitmap c) = 0
  large : BestFitFallback.LargeConditions (freeRegs sp size) c
  returnOutside : BestFitFallback.ReturnOutside (freeRegs sp size) c
  continuation : AllocSuccess.Conditions (AllocFinish.entryRegs sp size (resultHeader sp size c)) (allocated sp size c)

structure Input (sp size : BitVec 64) (c : Config) : Prop
    extends BestFitFallback.Input (freeRegs sp size) c, Conditions sp size c where
  ffsCode : Code.FfsLoaded c.σ.mem
  splitCode : Code.Bf_splitLoaded c.σ.mem
  wrapperCode : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  sizeRegister : gprGet c.σ 8 = some size

theorem Input.toMissingInput {sp size c} (input : Input sp size c) : BestFitFallback.MissingInput (freeRegs sp size) c :=
  { toInput := input.toInput
    small := input.small
    slotRead := input.slotRead
    empty := input.empty }

theorem resultHeader_of_memory {sp size before after} (memory : after.σ.mem = before.σ.mem) :
    resultHeader sp size after = resultHeader sp size before := BestFitFallback.largeHeader_of_memory memory

theorem freeEffect_of_memory {sp size before after} (memory : after.σ.mem = before.σ.mem) :
    freeEffect sp size after = freeEffect sp size before := BestFitFallback.completeEffect_of_memory memory

theorem allocated_memory {sp size before after} (memory : after.σ.mem = before.σ.mem) :
    (allocated sp size after).σ.mem = (allocated sp size before).σ.mem := by
  simp only [allocated,AllocFinish.snapshot,freeEffect_of_memory memory,memory]

theorem Conditions.of_memory {sp size before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions sp size before) : Conditions sp size after := by
  refine ⟨conditions.toMissingConditions.of_memory memory,conditions.tagRead,?_,
    conditions.large.of_memory memory,conditions.returnOutside.of_memory memory,?_⟩
  · simpa only [BestFitFallback.bitmap,memory] using conditions.emptyBitmap
  · rw [resultHeader_of_memory memory]
    exact conditions.continuation.of_memory (allocated_memory memory)

abbrev Post (sp size : BitVec 64) (before after : Config) : Prop :=
  AllocFinish.Post sp size (resultHeader sp size before) (freeEffect sp size before) before after

/-- Complete large-block free-list allocation followed by the same proved
color/header/accounting/native-return continuation used for exact-size lists. -/
theorem allocate {sp size c} (input : Input sp size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Post sp size c) := by
  constructor
  apply Vsa.Logic.Triple.seq (BestFitFallback.allocate_large input.toMissingInput input.ffsCode input.splitCode
    input.emptyBitmap input.large input.returnOutside (by change AllocEntry.returnPc.toNat % 4 = 0; decide)).run
  intro middle allocatedPost
  have kept : GHolds middle.σ [(8,size)] :=
    gholds_of_frame allocatedPost.native _ (by change KeysOK [8]; decide)
      (by change ∀ n ∈ [8], ∀ q ∈ noiseRegs, (q == gprReg n) = false; decide)
      (by change ∀ n ∈ [8], ∀ m ∈ [1,2,10,11,12,13,14,15], (gprReg m == gprReg n) = false; decide)
      ⟨input.sizeRegister,True.intro⟩
  have wrapperCode : Code.Caml_alloc_shr_for_minor_gcLoaded middle.σ.mem := by
    rw [allocatedPost.memory]
    apply image_writeLog Code.caml_alloc_shr_for_minor_gc_transport input.wrapperCode
    intro e member
    exact Nat.le_trans (by decide) (BestFitFallback.completeEffect_high input.toInput input.large e member)
  have callee : AllocFinish.CalleePost sp size (resultHeader sp size c) (freeEffect sp size c) c middle :=
    { good := allocatedPost.good
      tick := allocatedPost.tick
      minstret := allocatedPost.minstret
      code := wrapperCode
      pc := allocatedPost.pc
      registers := ⟨allocatedPost.stack,kept.1,allocatedPost.result,True.intro⟩
      memory := allocatedPost.memory
      output := allocatedPost.output
      native := allocatedPost.native }
  exact (callee.finish input.tagRead input.continuation).run middle ⟨allocatedPost.pc,rfl⟩

end OCaml.Vm.Gc.AllocLarge
