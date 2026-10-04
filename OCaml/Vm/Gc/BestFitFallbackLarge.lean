import OCaml.Vm.Gc.BestFitFallbackSaved
import OCaml.Vm.Gc.BestFitLarge

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initial memory after the fallback's three explicit native-save stores. -/
def searched (R : Nat → BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (effect R (bitmap c))}}

def largeEffect (R : Nat → BitVec 64) (c : Config) :=
  effect R (bitmap c) ++ BestFitLarge.splitEffect (frameSp R) (searched R c)

/-- Explicit initial-snapshot geometry for the large-list alternative.
The native/heap ownership invariant must supply it and stack/header separation. -/
structure LargeConditions (R : Nat → BitVec 64) (c : Config) : Prop where
  large : BestFitLarge.Conditions (frameSp R) (searched R c)
  headerOutside : OutLRange (BestFitLarge.effect (frameSp R)
    (BestFitLarge.size (frameSp R) (searched R c)) (BestFitLarge.header (searched R c)))
    (BestFitLarge.least (searched R c) - BitVec.ofNat 64 Layout.header_bytes).toNat 8

theorem searched_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    (searched R after).σ.mem = (searched R before).σ.mem := by
  simp only [searched,bitmap,memory]

theorem LargeConditions.of_memory {R before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : LargeConditions R before) : LargeConditions R after := by
  have same := searched_memory (R := R) memory
  refine ⟨conditions.large.of_memory same,?_⟩
  simpa only [BestFitLarge.size,BestFitLarge.header,BestFitLarge.least,word,same] using conditions.headerOutside

theorem largeEffect_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    largeEffect R after = largeEffect R before := by
  unfold largeEffect
  rw [BestFitLarge.splitEffect_of_memory (searched_memory memory)]
  simp only [bitmap,memory]

structure LargeSplit (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt BestFitLarge.call.link after
  result : gprGet after.σ 10 = some
    ((BestFitSplit.delta (BestFitLarge.size (frameSp R) (searched R before))
      (BestFitLarge.header (searched R before)) <<< (3 : Nat)) +
      BestFitSplit.headerAddr (BestFitLarge.least (searched R before)))
  stack : gprGet after.σ 2 = some (frameSp R)
  memory : after.σ.mem = writeLog before.σ.mem (largeEffect R before)
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Real allocator entry through the empty-list/bitmap alternative, least
large-block tests and complete split call. Final accounting/return follows. -/
theorem missing_large_split {R c} (input : MissingInput R c)
    (ffsCode : Code.FfsLoaded c.σ.mem) (splitCode : Code.Bf_splitLoaded c.σ.mem)
    (empty : filtered (R 10) (bitmap c) = 0) (conditions : LargeConditions R c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (LargeSplit R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (missing_search_zero input ffsCode empty).run
  intro middle searchedPost
  have memory : middle.σ.mem = (searched R c).σ.mem := by
    simpa only [searched] using searchedPost.memory
  have splitCode' : Code.Bf_splitLoaded middle.σ.mem := by
    rw [searchedPost.memory]
    apply image_writeLog Code.bf_split_transport splitCode
    intro e member
    exact Nat.le_trans (by decide) (effect_high input.toInput e member)
  have largeInput : BestFitLarge.Input (frameSp R) middle :=
    { toConditions := conditions.large.of_memory memory
      good := searchedPost.good
      tick := searchedPost.tick
      minstret := searchedPost.minstret
      code := searchedPost.code
      registers := ⟨searchedPost.stack,searchedPost.result,True.intro⟩ }
  have outside : OutLRange (BestFitLarge.effect (frameSp R) (BestFitLarge.size (frameSp R) middle)
      (BestFitLarge.header middle)) (BestFitLarge.least middle - BitVec.ofNat 64 Layout.header_bytes).toNat 8 := by
    simpa only [BestFitLarge.size,BestFitLarge.header,BestFitLarge.least,word,memory] using conditions.headerOutside
  have pc : PCAt BestFitLarge.pc middle := searchedPost.pc
  obtain ⟨after,run,result⟩ := (BestFitLarge.split largeInput splitCode' outside).run middle ⟨pc,rfl⟩
  refine ⟨after,run,⟨result.good,result.tick,result.minstret,result.pc,?_,result.stack,?_,result.code,
    result.output.trans searchedPost.output,?_⟩⟩
  · simpa only [BestFitLarge.size,BestFitLarge.header,BestFitLarge.least,word,memory] using result.result
  · rw [result.memory,BestFitLarge.splitEffect_of_memory memory,searchedPost.memory,
      largeEffect,writeLog_append]
  · intro r noise outside
    apply (result.native r noise (fun n hn => outside n (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))).trans
    apply searchedPost.native r noise
    intro n hn
    apply outside n
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn ⊢
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end OCaml.Vm.Gc.BestFitFallback
