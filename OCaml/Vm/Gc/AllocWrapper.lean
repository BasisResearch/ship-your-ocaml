import OCaml.Vm.Gc.AllocExact
import OCaml.Vm.Gc.AllocIndirect
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
  apply Vsa.Logic.Triple.seq (AllocEntry.prepare input.toInput).run
  intro atCall prologue
  have freeCode : Code.Bf_allocateLoaded atCall.σ.mem :=
    image_after Code.bf_allocate_transport (by decide) input.freeListCode
      (chainPlan_facts (AllocEntry.code_facts input.code) (AllocEntry.access input.toInput)) prologue.machine
  obtain ⟨callee,callRun,called⟩ := (AllocEntry.call_free_list prologue.machine.good prologue.machine.tick
    prologue.machine.minstret prologue.code prologue.registers (by decide)).run atCall ⟨prologue.pc,rfl⟩
  have calledMemory : callee.σ.mem = atCall.σ.mem := called.mem
  have memory : callee.σ.mem = (prepared R c).σ.mem := calledMemory.trans prologue.memory
  have freeConditions := input.freeList.of_memory memory
  have allocatedMemory := AllocExact.allocated_memory (size := R 10) memory
  have returnRegsSame := AllocExact.returnRegs_of_memory (sp := AllocEntry.frameSp R) (size := R 10) memory
  have continuation : AllocSuccess.Conditions
      (AllocExact.returnRegs (AllocEntry.frameSp R) (R 10) callee) (AllocExact.allocated (R 10) callee) := by
    rw [returnRegsSame]
    exact input.continuation.of_memory allocatedMemory
  have freeInput : AllocExact.Input (AllocEntry.frameSp R) (R 10) callee :=
    { toInput :=
      { toCoreInput :=
        { toCoreConditions := freeConditions.toCoreConditions
          good := called.good
          tick := called.tick
          minstret := called.minstret
          code := calledMemory ▸ freeCode
          registers := ⟨called.ra,gholds_lookup _ called.registers rfl,True.intro⟩
          aligned := by decide }
        repair := freeConditions.repair
        bitmap := freeConditions.bitmap }
      wrapperCode := calledMemory ▸ prologue.code
      nativePins := ⟨gholds_lookup _ called.registers rfl,gholds_lookup _ called.registers rfl,True.intro⟩
      tagRead := input.windows.tag.read
      continuation := continuation }
  obtain ⟨after,allocationRun,finished⟩ := (AllocExact.allocate freeInput).run callee ⟨called.pc,rfl⟩
  have saved (cell : Nat × Nat) (member : cell ∈ AllocEntry.saveCells) :
      bytesT (AllocExact.allocated (R 10) (prepared R c)).σ.mem
        (AllocEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8 = R cell.1 :=
    AllocEntry.saved_after c.σ.mem input.windows _ cell member (input.freeOutside cell member)
  have returnWord : AllocReturn.returnWord (AllocEntry.frameSp R)
      (AllocExact.resultHeader (R 10) callee) (AllocExact.allocated (R 10) callee) = R 1 := by
    unfold AllocReturn.returnWord
    rw [allocatedMemory]
    exact saved AllocReturn.slots.head! (AllocEntry.restore_cells _ (by decide))
  have headerSame : AllocExact.resultHeader (R 10) callee = AllocExact.resultHeader (R 10) (prepared R c) := by
    simp only [AllocExact.resultHeader,BestFitSmall.first,word,memory]
  have restored : AllocReturn.restored (AllocEntry.frameSp R) (AllocExact.resultHeader (R 10) callee)
      (AllocExact.allocated (R 10) callee) = callerRegs R (BestFitSmall.first (R 10) (prepared R c)) := by
    have stack : AllocEntry.frameSp R + AllocReturn.frameSize = R 2 := by
      change (R 2 + -AllocReturn.frameSize) + AllocReturn.frameSize = R 2
      rw [BitVec.add_neg_eq_sub,BitVec.sub_add_cancel]
    unfold AllocReturn.restored callerRegs
    rw [stack,headerSame]
    simp only [AllocExact.resultHeader,Layout.header_bytes,BitVec.sub_add_cancel]
    congr 2
    apply List.map_congr_left
    intro cell member
    rw [allocatedMemory]
    exact congrArg (fun value => (cell.1,value)) (saved cell (AllocEntry.restore_cells _ (List.mem_reverse.mp member)))
  refine ⟨after,callRun.trans allocationRun,⟨finished.good,finished.tick,finished.minstret,finished.code,
    ?_,?_,?_,?_,finished.output.trans (called.output.trans prologue.machine.output),?_⟩⟩
  · simpa only [returnWord] using finished.pc
  · simpa only [restored] using finished.registers
  · simpa only [BestFitSmall.first,word,memory] using finished.result
  · rw [finished.memory,AllocExact.effect_of_memory memory,memory]
    exact (writeLog_append c.σ.mem (AllocEntry.effect R) _).symm
  · intro r noise outside
    have prefixCover : ∀ n ∈ wrChain AllocEntry.blocks, n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
    exact (finished.native r noise outside).trans
      ((called.frame r noise (by simp [wrChain]) (outside 1 (by simp))).trans
        (prologue.machine.frame r noise (fun n hn => outside n (prefixCover n hn))))

/-- Full-wrapper final header agreement with its original size and tag. -/
theorem Post.header {R before after} (post : Post R before after) (input : Input R before)
    (separate : (AllocExact.resultHeader (R 10) (prepared R before)).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (AllocExact.resultHeader (R 10) (prepared R before)).toNat)
    (tagBound : (R 11).toNat < 256) :
    HeaderOk (word after (AllocExact.resultHeader (R 10) (prepared R before)).toNat) (R 10).toNat (R 11).toNat := by
  have memory : after.σ.mem = writeLog (prepared R before).σ.mem
      (AllocExact.effect (AllocEntry.frameSp R) (R 10) (prepared R before)) := by
    rw [post.memory,effect,writeLog_append]
    rfl
  have savedTag : word (AllocExact.allocated (R 10) (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat = R 11 :=
    AllocEntry.saved_after before.σ.mem input.windows _ (11,AllocEntry.tagOffset)
      (by simp [AllocEntry.saveCells]) (input.freeOutside _ (by simp [AllocEntry.saveCells]))
  have sizeBound : (R 10).toNat < 2^54 := by
    have small := input.small
    change (R 10).toNat ≤ 18014398509481983 at small
    omega
  have tagBound' : (word (AllocExact.allocated (R 10) (prepared R before))
      (AllocEntry.frameSp R + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256 := by
    rw [savedTag]
    exact tagBound
  have header := AllocExact.header_of_effect memory separate sizeBound tagBound'
  simpa only [savedTag] using header

end OCaml.Vm.Gc.AllocWrapper
