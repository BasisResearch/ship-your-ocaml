import OCaml.Vm.Gc.SingleFieldClassify
import OCaml.Vm.Gc.StoreReturn
import OCaml.Vm.Gc.OldifyReturn

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Both native return sequences restore the same decoded stack bank. -/
theorem StoreReturn.restored_of_savedSame {sp before after}
    (same : OldifyReturn.SavedSame sp before after) :
    StoreReturn.restored sp after = StoreReturn.restored sp before := by
  unfold StoreReturn.restored
  congr 1
  apply List.map_congr_left
  intro cell member
  have offsets : ∀ cell ∈ StoreReturn.slots, cell.2 ∈ OldifyReturn.offsets := by decide
  exact congrArg (fun value => (cell.1,value)) (same cell.2 (offsets cell (List.mem_reverse.mp member)))

namespace SingleField

def effect (q : PendingCopy) (root : BitVec 64) (c : Config) :=
  Enqueue.prefixLog q.source q.target root ++ StoreReturn.effect (child q root c) q.target

/-- Original native bank survives forwarding; the immediate child's final
store has the separately decoded return-path geometry. -/
structure ReturnConditions (q : PendingCopy) (root sp : BitVec 64) (c : Config) : Prop where
  windows : StoreReturn.Windows sp (child q root c) q.target
  prefixOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (Enqueue.prefixLog q.source q.target root) (sp + BitVec.ofNat 64 off).toNat 8
  aligned : (StoreReturn.returnWord sp c).toNat % 4 = 0
  immediate : ChildClassify.even (child q root c) = false

theorem child_of_memory {q root before after} (memory : after.σ.mem = before.σ.mem) :
    child q root after = child q root before := by
  simp only [child,WorkQueue.enqueueLoads,memory]

theorem effect_of_memory {q root before after} (memory : after.σ.mem = before.σ.mem) :
    effect q root after = effect q root before := by
  simp only [effect,child_of_memory memory]

theorem ReturnConditions.of_memory {q root sp before after} (memory : after.σ.mem = before.σ.mem)
    (conditions : ReturnConditions q root sp before) : ReturnConditions q root sp after := by
  constructor
  · simpa only [child_of_memory memory] using conditions.windows
  · exact conditions.prefixOutside
  · simpa only [StoreReturn.returnWord,word,memory] using conditions.aligned
  · simpa only [child_of_memory memory] using conditions.immediate

structure Returned (q : PendingCopy) (root sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (StoreReturn.returnWord sp before) after
  registers : GHolds after.σ (StoreReturn.restored sp before)
  memory : after.σ.mem = writeLog before.σ.mem (effect q root before)
  value : word after q.target.toNat = child q root before
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain StoreReturn.blocks ++ [8,9,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete single-field forwarding, child classification and native
store/return for an immediate child, with exact four-store effect. -/
theorem return_immediate {q root sp c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (conditions : ReturnConditions q root sp c) :
    FnSummary pc (fun d => d = c) (Returned q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_classify input).run
  intro middle classified
  have same := OldifyReturn.SavedSame.of_writeLog classified.memory conditions.prefixOutside
  have returnWord : StoreReturn.returnWord sp middle = StoreReturn.returnWord sp c := same.returnWord
  have stack' : gprGet middle.σ 2 = some sp :=
    (classified.native Register.x2 (by decide) (by decide)).trans stack
  have returnInput : StoreReturn.Input sp (child q root c) q.target middle :=
    ⟨classified.good,classified.tick,classified.minstret,classified.code,
      ⟨stack',gholds_lookup _ classified.registers rfl,classified.target,True.intro⟩,
      conditions.windows,returnWord ▸ conditions.aligned⟩
  have pc : PCAt StoreReturn.pc middle := by
    simpa only [conditions.immediate,ChildClassify.exitPc,StoreReturn.pc,Bool.false_eq_true,ite_false] using classified.pc
  obtain ⟨after,run,returned⟩ := (StoreReturn.finish returnInput).run middle ⟨pc,rfl⟩
  refine ⟨after,run,⟨returned.machine.good,returned.machine.tick,returned.machine.minstret,
    returned.code,?_,?_,?_,returned.value,returned.machine.output.trans classified.output,?_⟩⟩
  · simpa only [returnWord] using returned.pc
  · simpa only [StoreReturn.restored_of_savedSame same] using returned.registers
  · rw [returned.memory,classified.memory,effect,writeLog_append]
  · intro r noise outside
    exact (returned.machine.frame r noise (fun n hn => outside n (List.mem_append_left _ hn))).trans
      (classified.native r noise (fun n hn => outside n (List.mem_append_right _ hn)))

end SingleField
end OCaml.Vm.Gc
