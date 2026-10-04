import OCaml.Vm.Gc.BestFitFallbackLarge
import OCaml.Vm.Gc.BestFitLargeReturn

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def splitSnapshot (R : Nat → BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (largeEffect R c)}}

def largeHeader (R : Nat → BitVec 64) (c : Config) :=
  (BestFitSplit.delta (BestFitLarge.size (frameSp R) (searched R c))
    (BestFitLarge.header (searched R c)) <<< (3 : Nat)) +
    BestFitSplit.headerAddr (BestFitLarge.least (searched R c))

def completeEffect (R : Nat → BitVec 64) (c : Config) :=
  largeEffect R c ++ [(Layout.sym_caml_fl_cur_wsz,8,BestFitLargeReturn.counted (frameSp R) (splitSnapshot R c))]

/-- The original caller link survives every store after the fallback bank.
Heap/native-stack separation supplies this finite footprint obligation. -/
def ReturnOutside (R : Nat → BitVec 64) (c : Config) : Prop :=
  OutLRange (BestFitLarge.splitEffect (frameSp R) (searched R c))
    (frameSp R + BitVec.ofNat 64 BestFitLargeReturn.returnOffset).toNat 8

theorem largeHeader_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    largeHeader R after = largeHeader R before := by
  simp only [largeHeader,BestFitLarge.size,BestFitLarge.header,BestFitLarge.least,word,
    searched_memory memory]

theorem completeEffect_of_memory {R before after} (memory : after.σ.mem = before.σ.mem) :
    completeEffect R after = completeEffect R before := by
  simp only [completeEffect,largeEffect_of_memory memory,BestFitLargeReturn.counted,
    BestFitLargeReturn.savedSize,BestFitLargeReturn.savedRequest,word,splitSnapshot,
    largeEffect_of_memory memory,memory]

theorem ReturnOutside.of_memory {R before after} (memory : after.σ.mem = before.σ.mem)
    (outside : ReturnOutside R before) : ReturnOutside R after := by
  simpa only [ReturnOutside,BestFitLarge.splitEffect_of_memory (searched_memory memory)] using outside

theorem LargeSplit.returnWord {R before after} (post : LargeSplit R before after)
    (input : Input R before) (outside : ReturnOutside R before) :
    BestFitLargeReturn.returnWord (frameSp R) after = R 1 := by
  change bytesT after.σ.mem (frameSp R + BitVec.ofNat 64 BestFitLargeReturn.returnOffset).toNat 8 = _
  rw [post.memory,largeEffect,writeLog_append,bytesT_writeLog_out _ outside,effect_bank]
  exact saveShape.read before.σ.mem (frameSp R) (bankRegs R (bitmap before)) input.windows
    (saves.getLast!) (by decide)

theorem Input.return_windows {R c} (input : Input R c) : BestFitLargeReturn.Windows (frameSp R) :=
  ⟨(input.windows (saves[0]!) (by decide)).read,
   (input.windows (saves[1]!) (by decide)).read,
   (input.windows (saves[2]!) (by decide)).read⟩

/-- The split request is the original allocator argument, recovered from
its actual native-save log rather than supplied as a new observation. -/
theorem Input.searched_size {R c} (input : Input R c) :
    BestFitLarge.size (frameSp R) (searched R c) = R 10 := by
  change bytesT (writeLog c.σ.mem (effect R (bitmap c)))
    (frameSp R + BitVec.ofNat 64 BestFitLarge.sizeOffset).toNat 8 = _
  rw [effect_bank]
  exact saveShape.read c.σ.mem (frameSp R) (bankRegs R (bitmap c)) input.windows
    (saves[0]!) (by decide)

structure Allocated (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt (R 1) after
  result : gprGet after.σ 10 = some (largeHeader R before)
  stack : gprGet after.σ 2 = some (R 2)
  memory : after.σ.mem = writeLog before.σ.mem (completeEffect R before)
  counter : word after Layout.sym_caml_fl_cur_wsz = BestFitLargeReturn.counted (frameSp R) (splitSnapshot R before)
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,2,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete actual empty-small-list/zero-bitmap/least-large-block allocator
alternative, including split, accounting and original native caller return. -/
theorem allocate_large {R c} (input : MissingInput R c)
    (ffsCode : Code.FfsLoaded c.σ.mem) (splitCode : Code.Bf_splitLoaded c.σ.mem)
    (empty : filtered (R 10) (bitmap c) = 0) (conditions : LargeConditions R c)
    (outside : ReturnOutside R c) (aligned : (R 1).toNat % 4 = 0) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Allocated R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (missing_large_split input ffsCode splitCode empty conditions).run
  intro middle splitPost
  have memory : middle.σ.mem = (splitSnapshot R c).σ.mem := by
    simpa only [splitSnapshot] using splitPost.memory
  have ra := splitPost.returnWord input.toInput outside
  have finishInput : BestFitLargeReturn.Input (frameSp R) (largeHeader R c) middle :=
    ⟨splitPost.good,splitPost.tick,splitPost.minstret,splitPost.code,
      ⟨splitPost.stack,splitPost.result,True.intro⟩,input.toInput.return_windows,ra ▸ aligned⟩
  have pc : PCAt BestFitLargeReturn.pc middle := splitPost.pc
  obtain ⟨after,run,finished⟩ := (BestFitLargeReturn.finish finishInput).run middle ⟨pc,rfl⟩
  have countSame : BestFitLargeReturn.counted (frameSp R) middle =
      BestFitLargeReturn.counted (frameSp R) (splitSnapshot R c) := by
    simp only [BestFitLargeReturn.counted,BestFitLargeReturn.savedSize,BestFitLargeReturn.savedRequest,word,memory]
  have stackSame : frameSp R + BestFitLargeReturn.frameSize = R 2 := by
    change (R 2 - frameSize) + frameSize = R 2
    exact BitVec.sub_add_cancel _ _
  refine ⟨after,run,⟨finished.machine.good,finished.machine.tick,finished.machine.minstret,?_,finished.result,
    ?_,?_,?_,finished.code,finished.machine.output.trans splitPost.output,?_⟩⟩
  · simpa only [ra] using finished.pc
  · simpa only [stackSame] using finished.stack
  · rw [finished.memory,countSame,splitPost.memory,completeEffect,writeLog_append]
  · simpa only [countSame] using finished.counter
  · intro r noise untouched
    apply (finished.machine.frame r noise (fun n hn => untouched n (by
      have h := BestFitLargeReturn.written n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))).trans
    exact splitPost.native r noise untouched

/-- The carved header uses the original requested size. -/
theorem Allocated.requested {R before after} (post : Allocated R before after) (input : Input R before) :
    gprGet after.σ 10 = some
      ((BestFitSplit.delta (R 10) (BestFitLarge.header (searched R before)) <<< (3 : Nat)) +
        BestFitSplit.headerAddr (BestFitLarge.least (searched R before))) := by
  simpa only [largeHeader,input.searched_size] using post.result

end OCaml.Vm.Gc.BestFitFallback
