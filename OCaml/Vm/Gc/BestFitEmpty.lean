import OCaml.Vm.Gc.Generated.BestFitEmpty
import OCaml.Vm.Gc.BestFitRepair
import OCaml.Vm.Gc.BestFitBitmapReturn

namespace OCaml.Vm.Gc.BestFitEmpty
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable BestFitSmall

def route (size : BitVec 64) (c : Config) : Bool := decide (cursor size c = first size c)
def loads (size : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (slot size).toNat,
   read8 c.σ.mem (slot size + BitVec.ofNat 64 Layout.off_bf_small_merge).toNat,
   read8 c.σ.mem (first size c).toNat]
def effect (size : BitVec 64) (c : Config) : List WEntry :=
  (if route size c then repairLog size else []) ++ [((slot size).toNat,8,next size c)]

/-- Empty-successor entry conditions. Cursor repair is required only on
the selected branch; the prefix stores must preserve the later bitmap load. -/
structure Input (ra size : BitVec 64) (c : Config) : Prop extends CoreInput ra size c where
  tail : next size c = 0
  repair : cursor size c = first size c → RepairConditions size c
  bitmapOutside : OutLRange (effect size c) Layout.sym_bf_small_map 4

theorem pop_control_zero (ra size head cursor : BitVec 64) (b : List (BitVec 8))
    (zero : bytesVal .ld b = 0) :
    TermFactsO (runGM popZero.body (merged ra size head cursor) [b]) popZero.term := by
  rw [pop_regs]
  simpa [popZero,bf_allocateX7448FSeg,TermFactsO,TermFactsT,popped,srcVal,lookupG,guardB] using zero

theorem pop_access_zero (mem : Std.ExtHashMap Nat (BitVec 8)) (ra size head cursor : BitVec 64)
    (b : List (BitVec 8)) (read : ReadWindow head 8) (write : WriteWindow (slot size) 8)
    (pins : LPins8 mem head.toNat b) (zero : bytesVal .ld b = 0) :
    ChainAccess mem (merged ra size head cursor) [b] [popZero] := by
  exact ChainAccess.cons (b := popZero)
    ⟨BestFitSmall.pop_access _ _ _ _ _ _ _ read write pins,pop_control_zero _ _ _ _ _ zero⟩ ChainAccess.nil

theorem access {ra size c} (input : Input ra size c) :
    ChainAccess c.σ.mem (regs ra size) (loads size c) (blocks (route size c)) := by
  apply ChainAccess.append_eval (state := SegEvalState.init (regs ra size) (loads size c))
    (left := entryBlocks)
    (right := (if route size c then [repairTest,repairBlock] else [mergeBlock]) ++ [popZero])
  · change ChainAccess c.σ.mem (regs ra size) (loads size c) entryBlocks
    apply entry_access _ _ _ _ _ input.headWrite.read (read8_pins _ _) input.small
    simpa only [read8_value,first,word] using input.head
  · simp only [loads,entry_eval,read8_value]
    change ChainAccess c.σ.mem (listed ra size (first size c)) _ _
    by_cases repair : cursor size c = first size c
    · simp only [route,repair,decide_true,ite_true,List.cons_append,List.nil_append]
      apply ChainAccess.cons (b := repairTest) ⟨merge_access _ _ _ _ _ _ input.mergeRead (read8_pins _ _),?_⟩
      · rw [repair_test_log,repair_test_regs,repair_test_loads]
        simp only [read8_value]
        change ChainAccess c.σ.mem (merged ra size (first size c) (cursor size c)) _ _
        apply ChainAccess.cons ⟨repair_access _ _ _ _ _ _ (input.repair repair).mergeWrite,True.intro⟩
        rw [repair_log,repair_regs,repair_loads]
        apply pop_access_zero _ _ _ _ _ _ input.nextRead input.headWrite
          (lpins8_writeLog (read8_pins _ _) (input.repair repair).nextOutside)
        simpa only [read8_value,next,word] using input.tail
      · apply repair_test_control
        simpa only [read8_value,cursor,first,word] using repair
    · simp only [route,repair,decide_false,ite_false,List.cons_append,List.nil_append]
      apply ChainAccess.cons ⟨merge_access _ _ _ _ _ _ input.mergeRead (read8_pins _ _),?_⟩
      · rw [merge_log,merge_regs,merge_loads]
        simp only [read8_value]
        change ChainAccess c.σ.mem (merged ra size (first size c) (cursor size c)) _ _
        apply pop_access_zero _ _ _ _ _ _ input.nextRead input.headWrite (read8_pins _ _)
        simpa only [read8_value,next,word] using input.tail
      · apply merge_control
        simpa only [read8_value,cursor,first,word] using repair

/-- The complete empty-successor prefix is parked at the bitmap block,
with the common return interface and later global observations preserved. -/
structure EntryPost (ra size : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks (route size before)) BestFitSmall.pc (regs ra size) (loads size before) before after
  memory : after.σ.mem = writeLog before.σ.mem (effect size before)
  pc : PCAt BestFitBitmap.pc after
  registers : GHolds after.σ (BestFitFinish.regs ra size (first size before))
  code : Code.Bf_allocateLoaded after.σ.mem
  bitmap : word32 after Layout.sym_bf_small_map = word32 before Layout.sym_bf_small_map
  counter : word after Layout.sym_caml_fl_cur_wsz = word before Layout.sym_caml_fl_cur_wsz

theorem Input.counter_outside {ra size c} (input : Input ra size c) :
    OutLRange (effect size c) Layout.sym_caml_fl_cur_wsz 8 := by
  by_cases repair : cursor size c = first size c
  · simp only [effect,route,repair,decide_true,ite_true]
    exact ⟨(input.repair repair).counterOutside.1,input.counterOutside⟩
  · simpa only [effect,route,repair,decide_false,Bool.false_eq_true,ite_false,List.nil_append] using input.counterOutside

/-- Execute the exact-size empty-successor prefix and either observed
cursor branch, through the actual branch into bitmap clearing. -/
theorem prepare {ra size c} (input : Input ra size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (EntryPost ra size c) := by
  have facts := chainPlan_facts (code_facts (route size c) input.code) (access input)
  have summary := block_summary (blocks (route size c)) BestFitSmall.pc (regs ra size) (loads size c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10]; decide,
      facts,chain_ok _,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem (effect size c) := by
    rw [post.memory,loads,writes]
    simp only [effect,next,word,read8_value]
  refine ⟨post,memory,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post,?_,?_⟩
  · rw [PCAt,post.pc,loads,endpoint]
  · have pins := post.regs
    rw [loads,registers] at pins
    simp only [read8_value] at pins
    exact ⟨gholds_lookup _ pins rfl,gholds_lookup _ pins rfl,gholds_lookup _ pins rfl,True.intro⟩
  · unfold word32
    rw [memory]
    exact bytesT_writeLog_out _ input.bitmapOutside
  · unfold word
    rw [memory]
    exact bytesT_writeLog_out _ input.counter_outside

def allocationEffect (size : BitVec 64) (c : Config) : List WEntry :=
  effect size c ++
    ([(Layout.sym_bf_small_map,4,BestFitBitmap.cleared size
      (bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map)))] ++ BestFitFinish.effect size c)

/-- A complete exact-size allocation with an emptied successor, including
optional cursor repair, bitmap clearing, accounting and native return. -/
structure Post (ra size : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Bf_allocateLoaded after.σ.mem
  pc : PCAt ra after
  result : gprGet after.σ 10 = some (first size before - BitVec.ofNat 64 Layout.header_bytes)
  memory : after.σ.mem = writeLog before.σ.mem (allocationEffect size before)
  bitmap : word32 after Layout.sym_bf_small_map =
    word32 before Layout.sym_bf_small_map &&& ~~~(1#32 <<< (size.toNat - 1))
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Function entry through native return for both empty-successor cursor
cases, composed solely from decoded machine summaries and initial observations. -/
theorem allocate {ra size c} (input : Input ra size c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Post ra size c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle prepared
  have bitmapInput : BestFitBitmap.ReturnInput ra size (first size c) middle :=
    ⟨⟨prepared.machine.good,prepared.machine.tick,prepared.machine.minstret,prepared.code,
      ⟨gholds_lookup _ prepared.registers rfl,True.intro⟩,input.positive,input.small⟩,
      prepared.registers,input.aligned⟩
  obtain ⟨after,run,finished⟩ := (BestFitBitmap.clear_return bitmapInput).run middle ⟨prepared.pc,rfl⟩
  refine ⟨after,run,⟨finished.good,finished.tick,finished.minstret,finished.code,finished.pc,
    finished.result,?_,?_,finished.output.trans prepared.machine.output,?_⟩⟩
  · have observed : bytesVal .lw (read4 middle.σ.mem Layout.sym_bf_small_map) =
        bytesVal .lw (read4 c.σ.mem Layout.sym_bf_small_map) := by
      rw [read4_value,read4_value]
      exact congrArg (Functions.sign_extend (m := 64)) prepared.bitmap
    rw [finished.memory,observed,BestFitFinish.effect,prepared.counter,prepared.memory,
      allocationEffect]
    simp only [writeLog_append,BestFitFinish.effect]
  · rw [finished.bitmap,prepared.bitmap]
  · intro r noise outside
    have later : ∀ n ∈ [10,12,13,14,15], n ∈ [10,11,12,13,14,15] := by decide
    have earlier : ∀ n ∈ [11,12,13,14,15], n ∈ [10,11,12,13,14,15] := by decide
    exact (finished.native r noise (fun n hn => outside n (later n hn))).trans
      (prepared.machine.frame r noise (fun n hn => outside n (earlier n (written _ n hn))))

/-- Bitmap clearing and cursor repair do not change the accounting formula. -/
theorem Post.counter {ra size before after} (post : Post ra size before after) :
    total after = total before - 1#64 - size := by
  unfold total word
  rw [post.memory,allocationEffect,BestFitFinish.effect,writeLog_append,writeLog_append]
  exact word_writeLog _ _ _

end OCaml.Vm.Gc.BestFitEmpty
