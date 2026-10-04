import OCaml.Vm.Gc.BestFitExact
import OCaml.Vm.Gc.AllocSuccess
import Vsa.Sim.GRegsFrame

namespace OCaml.Vm.Gc.AllocExact
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The exact-size allocator has a deterministic, reflected write log.
This snapshot is only for stating subsequent memory observations. -/
def allocated (size : BitVec 64) (c : Config) : Config :=
  { c with σ := { c.σ with mem := writeLog c.σ.mem (BestFitExact.effect size c) } }

def resultHeader (size : BitVec 64) (c : Config) :=
  BestFitSmall.first size c - BitVec.ofNat 64 Layout.header_bytes

def returnRegs (sp size : BitVec 64) (c : Config) (n : Nat) :=
  if n = 2 then sp else if n = 8 then size else resultHeader size c

theorem returnRegs_of_memory {sp size} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    returnRegs sp size after = returnRegs sp size before := by
  funext n
  simp only [returnRegs,resultHeader,BestFitSmall.first,word,memory]

theorem allocated_memory {size} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    (allocated size after).σ.mem = (allocated size before).σ.mem := by
  change writeLog after.σ.mem (BestFitExact.effect size after) = writeLog before.σ.mem (BestFitExact.effect size before)
  rw [memory,BestFitExact.effect_of_memory memory]

/-- Combined reflected effect of the free-list callee and wrapper continuation. -/
def effect (sp size : BitVec 64) (c : Config) : List WEntry :=
  BestFitExact.effect size c ++ AllocAccount.effect
    (AllocSuccess.completed (returnRegs sp size c) (allocated size c)) (allocated size c)

theorem effect_of_memory {sp size} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    effect sp size after = effect sp size before := by
  have allocatedSame := allocated_memory (size := size) memory
  unfold effect
  rw [BestFitExact.effect_of_memory memory,returnRegs_of_memory memory,
    AllocSuccess.completed_of_memory allocatedSame]
  simp only [AllocAccount.effect,AllocAccount.counted,AllocAccount.initialized,allocatedSame]

/-- Real free-list entry conditions plus memory observations of its exact
store log. No premise asserts execution of the allocator or continuation. -/
structure Input (sp size : BitVec 64) (c : Config) : Prop
    extends BestFitExact.Input AllocEntry.returnPc size c where
  wrapperCode : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  nativePins : GHolds c.σ [(2,sp),(8,size)]
  tagRead : ReadWindow (sp + BitVec.ofNat 64 AllocEntry.tagOffset) 8
  continuation : AllocSuccess.Conditions (returnRegs sp size c) (allocated size c)

structure Post (sp size : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem
  pc : PCAt (AllocReturn.returnWord sp (resultHeader size before) (allocated size before)) after
  registers : GHolds after.σ (AllocReturn.restored sp (resultHeader size before) (allocated size before))
  result : gprGet after.σ 10 = some (BestFitSmall.first size before)
  memory : after.σ.mem = writeLog before.σ.mem (effect sp size before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Exact-size best-fit allocation followed by the actual wrapper's color,
accounting and return path. All four small-list cases and all colors are covered. -/
theorem allocate {sp size c} (input : Input sp size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Post sp size c) := by
  constructor
  apply Vsa.Logic.Triple.seq (BestFitExact.allocate input.toInput).run
  intro middle allocatedPost
  have memory : middle.σ.mem = (allocated size c).σ.mem := allocatedPost.memory
  have pins : GHolds middle.σ [(2,sp),(8,size)] :=
    gholds_of_frame allocatedPost.native _ (by change KeysOK [2,8]; decide)
      (by change ∀ n ∈ [2,8], ∀ q ∈ noiseRegs, (q == gprReg n) = false; decide)
      (by change ∀ n ∈ [2,8], ∀ m ∈ [10,11,12,13,14,15], (gprReg m == gprReg n) = false; decide)
      input.nativePins
  have wrapperCode : Code.Caml_alloc_shr_for_minor_gcLoaded middle.σ.mem := by
    rw [allocatedPost.memory]
    apply image_writeLog Code.caml_alloc_shr_for_minor_gc_transport input.wrapperCode
    intro e member
    have bound := BestFitExact.effect_high input.toInput e member
    exact Nat.le_trans (by decide) bound
  have nonnull : resultHeader size c ≠ 0 := by
    have lower := input.nextRead.lower
    have bound := (BestFitSmall.first size c).isLt
    unfold resultHeader
    change BestFitSmall.first size c - 8#64 ≠ 0
    bv_omega
  have finishInput : AllocSuccess.Input (returnRegs sp size c) middle :=
    { toInput :=
      { good := allocatedPost.good
        tick := allocatedPost.tick
        minstret := allocatedPost.minstret
        code := wrapperCode
        registers := ⟨pins.1,pins.2.1,allocatedPost.result,True.intro⟩
        tagRead := input.tagRead
        nonnull := nonnull }
      toConditions := input.continuation.of_memory memory }
  obtain ⟨after,run,finished⟩ := (AllocSuccess.finish finishInput).run middle ⟨allocatedPost.pc,rfl⟩
  refine ⟨after,run,⟨finished.good,finished.tick,finished.minstret,finished.code,?_,?_,?_,?_,
    finished.output.trans allocatedPost.output,?_⟩⟩
  · simpa [AllocReturn.returnWord,returnRegs,memory] using finished.pc
  · simpa [AllocReturn.restored,returnRegs,memory] using finished.registers
  · have result := finished.result
    simpa [returnRegs,resultHeader,BitVec.sub_add_cancel] using result
  · have same := AllocSuccess.completed_of_memory (R := returnRegs sp size c) memory
    rw [finished.memory,same]
    unfold effect
    simp only [AllocAccount.effect,AllocAccount.counted,AllocAccount.initialized,memory,allocated,writeLog_append]
  · intro r noise outside
    have finishCover : ∀ n ∈ [1,2,8,9,10,11,13,14,15], n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
    have allocateCover : ∀ n ∈ [10,11,12,13,14,15], n ∈ [1,2,8,9,10,11,12,13,14,15] := by decide
    exact (finished.native r noise (fun n hn => outside n (finishCover n hn))).trans
      (allocatedPost.native r noise (fun n hn => outside n (allocateCover n hn)))

/-- The final header store carries the requested size and the tag saved by
the wrapper, provided accounting does not alias that header. -/
theorem header_of_effect {sp size} {before after : Config}
    (memory : after.σ.mem = writeLog before.σ.mem (effect sp size before))
    (separate : (resultHeader size before).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (resultHeader size before).toNat)
    (sizeBound : size.toNat < 2^54)
    (tagBound : (word (allocated size before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat < 256) :
    HeaderOk (word after (resultHeader size before).toNat) size.toNat
      (word (allocated size before) (sp + BitVec.ofNat 64 AllocEntry.tagOffset).toNat).toNat := by
  have stored : word after (resultHeader size before).toNat =
      AllocSuccess.completed (returnRegs sp size before) (allocated size before) 11 := by
    rw [word,memory,effect,writeLog_append]
    apply word_writeLog_at _ _ 0 _ _ rfl
    exact ⟨separate,True.intro⟩
  rw [stored]
  exact AllocColor.header_ok _ _ _ sizeBound tagBound

end OCaml.Vm.Gc.AllocExact
