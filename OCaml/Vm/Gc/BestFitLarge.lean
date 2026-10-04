import OCaml.Vm.Gc.BestFitLargeAccess
import OCaml.Vm.Gc.BestFitSplit
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Gc.BestFitLarge
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

structure Prepared (sp : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs sp) (loads sp before) before after
  pc : PCAt call.pc after
  registers : GHolds after.σ (atCall sp (bits sp before) (size sp before) (least before) (header before))
  memory : after.σ.mem = writeLog before.σ.mem (effect sp (size sp before) (header before))
  code : Code.Bf_allocateLoaded after.σ.mem

/-- Execute actual saved-size reload, nonnull least-block test, size test
and native stores up to the bf_split call. -/
theorem prepare {sp c} (input : Input sp c) :
    FnSummary pc (fun d => d = c) (Prepared sp c) := by
  have facts := chainPlan_facts (code_facts input.code) (access input)
  have summary := block_summary blocks pc (regs sp) (loads sp c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,10]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_allocate_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,endpoint]
  · simpa only [loads,registers,read8_value,bits,size,least,header,word] using post.regs
  · rw [post.memory,loads,writes]
    simp only [read8_value,size,header,word]

/-- Explicit snapshot after the two decoded pre-split stack stores. -/
def prepared (sp : BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (effect sp (size sp c) (header c))}}

def splitEffect (sp : BitVec 64) (c : Config) :=
  effect sp (size sp c) (header c) ++ BestFitSplit.effect (size sp c) (least c) (prepared sp c)

structure Split (sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  pc : PCAt call.link after
  result : gprGet after.σ 10 = some ((BestFitSplit.delta (size sp before) (header before) <<< (3 : Nat)) +
    BestFitSplit.headerAddr (least before))
  stack : gprGet after.σ 2 = some sp
  memory : after.σ.mem = writeLog before.σ.mem (splitEffect sp before)
  code : Code.Bf_allocateLoaded after.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [1,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- The complete least-large-block prefix and actual split callee. Stack
writes are separated from the remnant header by the allocator ownership
premise; there is no assumed callee execution. -/
theorem split {sp c} (input : Input sp c) (splitCode : Code.Bf_splitLoaded c.σ.mem)
    (outside : OutLRange (effect sp (size sp c) (header c))
      (least c - BitVec.ofNat 64 Layout.header_bytes).toNat 8) :
    FnSummary pc (fun d => d = c) (Split sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle preparedPost
  have splitCode' : Code.Bf_splitLoaded middle.σ.mem :=
    image_after Code.bf_split_transport (by decide) splitCode
      (chainPlan_facts (code_facts input.code) (access input)) preparedPost.machine
  let pins : GRegs := [(2,sp),(10,size sp c),(11,least c)]
  have holds : GHolds middle.σ pins :=
    ⟨gholds_lookup _ preparedPost.registers rfl,gholds_lookup _ preparedPost.registers rfl,
      gholds_lookup _ preparedPost.registers rfl,True.intro⟩
  have callSummary := call_summary call_shape call_decode middle (call_pins preparedPost.code)
    preparedPost.machine.good preparedPost.machine.tick preparedPost.machine.minstret pins holds
    (by change KeysOK [2,10,11]; decide) (by change ∀ n ∈ [2,10,11], n ≠ 1; decide)
  obtain ⟨callee,callRun,called⟩ := callSummary.run middle ⟨preparedPost.pc,rfl⟩
  have calleeInput : BestFitSplit.Input call.link (size sp c) (least c) callee :=
    ⟨called.good,called.tick,called.minstret,called.mem ▸ splitCode',
      ⟨called.ra,gholds_lookup _ called.registers rfl,gholds_lookup _ called.registers rfl,True.intro⟩,
      input.headerWrite,by decide⟩
  have calleePc : PCAt BestFitSplit.pc callee := by simpa only [PCAt,call_target] using called.pc
  obtain ⟨after,run,result⟩ := (BestFitSplit.split calleeInput).run callee ⟨calleePc,rfl⟩
  have calledMemory : callee.σ.mem = middle.σ.mem := called.mem
  have memory : callee.σ.mem = (prepared sp c).σ.mem := by
    rw [calledMemory,preparedPost.memory]
    rfl
  have headerSame : BestFitSplit.header (least c) callee = header c := by
    change bytesT callee.σ.mem (least c - BitVec.ofNat 64 Layout.header_bytes).toNat 8 = _
    rw [calledMemory,preparedPost.memory,bytesT_writeLog_out _ outside]
    rfl
  refine ⟨after,callRun.trans run,⟨result.machine.good,result.machine.tick,result.machine.minstret,
    result.pc,?_,?_,?_,?_,result.machine.output.trans (called.output.trans preparedPost.machine.output),?_⟩⟩
  · simpa only [headerSame] using result.result
  · have same := result.machine.frame Register.x2 (by decide) (fun n hn => by
      have h := BestFitSplit.written _ n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> decide)
    have stack : gprGet callee.σ 2 = some sp := gholds_lookup _ called.registers rfl
    exact same.trans stack
  · rw [result.memory]
    simp only [BestFitSplit.effect,BestFitSplit.header,word,memory]
    rw [splitEffect,writeLog_append]
    rfl
  · exact image_after Code.bf_allocate_transport (by decide) (called.mem ▸ preparedPost.code)
      (chainPlan_facts (BestFitSplit.code_facts _ calleeInput.code) (BestFitSplit.access calleeInput)) result.machine
  · intro r noise untouched
    apply (result.machine.frame r noise (fun n hn => untouched n (by
      have h := BestFitSplit.written _ n hn
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp))).trans
    apply (called.frame r noise (by simp [wrChain]) (untouched 1 (by simp))).trans
    apply preparedPost.machine.frame r noise
    intro n hn
    have h := written n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> apply untouched _ (by simp)

end OCaml.Vm.Gc.BestFitLarge
