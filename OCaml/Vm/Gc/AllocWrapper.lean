import OCaml.Vm.Gc.AllocExact
import OCaml.Vm.Gc.AllocWrapperCore
import OCaml.Vm.Gc.AllocSaved

namespace OCaml.Vm.Gc.AllocWrapper
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Memory observations after the explicit wrapper prologue store log. -/
def prepared (R : Nat → BitVec 64) (c : Config) : Config :=
  { c with σ := { c.σ with mem := writeLog c.σ.mem (AllocEntry.effect R) } }

/-- Successful exact-size allocation from the wrapper's real entry.
All later conditions describe explicit initial-memory write-log snapshots. -/
structure Conditions (R : Nat → BitVec 64) (c : Config) : Prop where
  freeList : BestFitExact.Conditions (R 10) (prepared R c)
  freeOutside : ∀ cell ∈ AllocEntry.saveCells, OutLRange (BestFitExact.effect (R 10) (prepared R c))
    (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8
  continuation : AllocSuccess.Conditions
    (AllocExact.returnRegs (AllocEntry.frameSp R) (R 10) (prepared R c))
    (AllocExact.allocated (R 10) (prepared R c))


structure Input (R : Nat → BitVec 64) (c : Config) : Prop
    extends AllocEntry.Input R BestFitSmall.pc c, Conditions R c where
  freeListCode : Code.Bf_allocateLoaded c.σ.mem

theorem prepared_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    (prepared R after).σ.mem = (prepared R before).σ.mem := by simp only [prepared,memory]

theorem Conditions.of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions R before) : Conditions R after := by
  have same := prepared_memory (R := R) memory
  constructor
  · exact conditions.freeList.of_memory same
  · simpa only [BestFitExact.effect_of_memory same] using conditions.freeOutside
  · rw [AllocExact.returnRegs_of_memory same]
    exact conditions.continuation.of_memory (AllocExact.allocated_memory same)

def callerRegs (R : Nat → BitVec 64) (payload : BitVec 64) : GRegs :=
  (2,R 2) :: (10,payload) :: AllocReturn.slots.reverse.map (fun cell => (cell.1,R cell.1))

def effect (R : Nat → BitVec 64) (c : Config) :=
  AllocEntry.effect R ++ AllocExact.effect (AllocEntry.frameSp R) (R 10) (prepared R c)

theorem effect_of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    effect R after = effect R before := by
  unfold effect
  rw [AllocExact.effect_of_memory (prepared_memory memory)]

structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (callerRegs R (BestFitSmall.first (R 10) (prepared R before)))
  result : gprGet after.σ 10 = some (BestFitSmall.first (R 10) (prepared R before))
  memory : after.σ.mem = writeLog before.σ.mem (effect R before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete real wrapper prologue, loaded JALR, exact-size free-list
allocation, color selection, header/accounting writes and caller return. -/
theorem allocate {R c} (input : Input R c) :
    FnSummary AllocEntry.pc (fun d => d = c) (Post R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (AllocWrapperCore.enter input.toInput).run
  intro callee entered
  have memory : callee.σ.mem = (prepared R c).σ.mem := entered.memory
  have freeCode := entered.image input.windows Code.bf_allocate_transport (by decide) input.freeListCode
  have freeConditions := input.freeList.of_memory memory
  have continuation : AllocSuccess.Conditions
      (AllocExact.returnRegs (AllocEntry.frameSp R) (R 10) callee) (AllocExact.allocated (R 10) callee) := by
    rw [AllocExact.returnRegs_of_memory memory]
    exact input.continuation.of_memory (AllocExact.allocated_memory memory)
  have freeInput : AllocExact.Input (AllocEntry.frameSp R) (R 10) callee :=
    { toInput :=
      { toCoreInput :=
        { toCoreConditions := freeConditions.toCoreConditions
          good := entered.good
          tick := entered.tick
          minstret := entered.minstret
          code := freeCode
          registers := ⟨entered.link,gholds_lookup _ entered.registers rfl,True.intro⟩
          aligned := by decide }
        repair := freeConditions.repair
        bitmap := freeConditions.bitmap }
      wrapperCode := entered.code
      nativePins := ⟨gholds_lookup _ entered.registers rfl,gholds_lookup _ entered.registers rfl,True.intro⟩
      tagRead := input.windows.tag.read
      continuation := continuation }
  obtain ⟨after,run,finished⟩ := (AllocExact.allocate freeInput).run callee ⟨entered.pc,rfl⟩
  have logSame := BestFitExact.effect_of_memory (size := R 10) memory
  have headerSame : AllocExact.resultHeader (R 10) callee = AllocExact.resultHeader (R 10) (prepared R c) := by
    simp only [AllocExact.resultHeader,BestFitSmall.first,word,memory]
  have outside : ∀ cell ∈ AllocEntry.saveCells, OutLRange (BestFitExact.effect (R 10) callee)
      (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 := by
    simpa only [logSame] using input.freeOutside
  have complete := entered.complete input.windows outside finished.toFinished
  refine ⟨after,run,⟨complete.good,complete.tick,complete.minstret,complete.code,complete.pc,?_,?_,?_,
    complete.output,complete.native⟩⟩
  · have pins := complete.registers
    rw [headerSame] at pins
    simpa only [AllocExact.resultHeader,BitVec.sub_add_cancel,AllocWrapperCore.callerRegs,callerRegs] using pins
  · have result := complete.result
    rw [headerSame] at result
    simpa only [AllocExact.resultHeader,BitVec.sub_add_cancel] using result
  · have memory' := complete.memory
    rw [headerSame,logSame] at memory'
    have same : AllocFinish.entryRegs (AllocEntry.frameSp R) (R 10)
        (AllocExact.resultHeader (R 10) (prepared R c)) =
        AllocExact.returnRegs (AllocEntry.frameSp R) (R 10) (prepared R c) := rfl
    unfold AllocWrapperCore.effect AllocFinish.effect at memory'
    rw [same] at memory'
    have snapshotSame : AllocWrapperCore.prepared R c = prepared R c := rfl
    rw [snapshotSame] at memory'
    simpa only [AllocFinish.snapshot,AllocExact.effect,effect,AllocExact.allocated] using memory'

theorem effect_eq_core (R : Nat → BitVec 64) (c : Config) :
    effect R c = AllocWrapperCore.effect R (AllocExact.resultHeader (R 10) (prepared R c))
      (BestFitExact.effect (R 10) (prepared R c)) c := rfl

theorem Post.toCore {R before after} (post : Post R before after) :
    AllocWrapperCore.Post R (AllocExact.resultHeader (R 10) (prepared R before))
      (BestFitExact.effect (R 10) (prepared R before)) before after := by
  refine ⟨post.good,post.tick,post.minstret,post.code,post.pc,?_,?_,?_,post.output,post.native⟩
  · simpa only [AllocExact.resultHeader,BitVec.sub_add_cancel,callerRegs,AllocWrapperCore.callerRegs] using post.registers
  · simpa only [AllocExact.resultHeader,BitVec.sub_add_cancel] using post.result
  · simpa only [effect_eq_core] using post.memory

/-- Full-wrapper final header agreement with its original size and tag. -/
theorem header_of_effect {R} {before after : Config}
    (memory : after.σ.mem = writeLog before.σ.mem (effect R before))
    (windows : AllocEntry.Windows R) (conditions : Conditions R before)
    (sizeBound : (R 10).toNat < 2^54)
    (separate : (AllocExact.resultHeader (R 10) (prepared R before)).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (AllocExact.resultHeader (R 10) (prepared R before)).toNat)
    (tagBound : (R 11).toNat < 256) :
    HeaderOk (word after (AllocExact.resultHeader (R 10) (prepared R before)).toNat) (R 10).toNat (R 11).toNat := by
  have memory : after.σ.mem = writeLog (prepared R before).σ.mem
      (AllocExact.effect (AllocEntry.frameSp R) (R 10) (prepared R before)) := by
    rw [memory,effect,writeLog_append]
    rfl
  have savedTag : word (AllocExact.allocated (R 10) (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat = R 11 :=
    AllocEntry.saved_after before.σ.mem windows _ (11,AllocEntry.tagOffset)
      (by simp [AllocEntry.saveCells]) (conditions.freeOutside _ (by simp [AllocEntry.saveCells]))
  have tagBound' : (word (AllocExact.allocated (R 10) (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256 := by
    rw [savedTag]
    exact tagBound
  have header := AllocExact.header_of_effect memory separate sizeBound tagBound'
  simpa only [savedTag] using header


/-- Full-wrapper final header agreement with its original size and tag. -/
theorem Post.header {R before after} (post : Post R before after) (input : Input R before)
    (separate : (AllocExact.resultHeader (R 10) (prepared R before)).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (AllocExact.resultHeader (R 10) (prepared R before)).toNat)
    (tagBound : (R 11).toNat < 256) :
    HeaderOk (word after (AllocExact.resultHeader (R 10) (prepared R before)).toNat) (R 10).toNat (R 11).toNat := by
  apply header_of_effect post.memory input.windows input.toConditions _ separate tagBound
  have small := input.small
  change (R 10).toNat ≤ 18014398509481983 at small
  omega

end OCaml.Vm.Gc.AllocWrapper
