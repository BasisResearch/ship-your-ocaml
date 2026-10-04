import OCaml.Vm.Gc.SingleFieldFresh
import OCaml.Vm.Gc.ContextLargeAllocated

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

structure LargeFreshChildConditions (q : PendingCopy) (root sp : BitVec 64) (size tag : Nat) (c : Config) : Prop
    extends FreshChildHeader q root sp size tag c where
  allocation : Fresh.ContextLargeConditions (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)

abbrev ChildLargeAllocated (q : PendingCopy) (root sp : BitVec 64) (before after : Config) :=
  Fresh.ContextAllocated (child q root before) q.target sp (childHeader q root before)
    (Fresh.contextLargePayload (child q root before) q.target sp (childHeader q root before) (forwardedSnapshot q root before))
    (Enqueue.prefixLog q.source q.target root ++
      AllocLargeWrapper.effect (childAllocatorRegs q root sp before) (forwardedSnapshot q root before)) before after
    ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15]))

/-- The same captured-child boundary may use the complete least-large-block
allocation alternative. Its frame and parent-prefix composition are shared. -/
theorem YoungHead.allocate_child_large {q root sp size tag before middle}
    (head : YoungHead q root sp before middle) (conditions : LargeFreshChildConditions q root sp size tag before) :
    FnSummary Fresh.pc (fun d => d = middle)
      (ChildLargeAllocated q root sp before) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := head.memory
  have headerSame : word middle (child q root before - 8#64).toNat = childHeader q root before := by
    simp only [childHeader,word,memory]
  have allocation : Fresh.ContextLargeConditions
      (Fresh.contextRegs (child q root before) q.target sp (word middle (child q root before - 8#64).toNat)) middle := by
    rw [headerSame]
    exact conditions.allocation.of_memory memory
  apply (Fresh.allocate_context_large (head.fresh_input conditions.toFreshChildHeader) head.context_carried allocation).weaken (fun _ h => h)
  intro after allocated
  rw [headerSame,Fresh.contextLargePayload_of_memory memory,AllocLargeWrapper.effect_of_memory memory] at allocated
  exact head.complete_allocation allocated

/-- Parent forwarding followed by the child's least-large-block allocation. -/
theorem prepare_allocate_child_large {q root sp domain size tag c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c)
    (conditions : LargeFreshChildConditions q root sp size tag c) :
    FnSummary pc (fun d => d = c) (ChildLargeAllocated q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_young input stack constants even range).run
  intro middle head
  have pc : PCAt Fresh.pc middle := by
    simpa only [OldifyYoung.exitPc,Fresh.pc] using head.pc
  exact (head.allocate_child_large conditions).run middle ⟨pc,rfl⟩

end OCaml.Vm.Gc.SingleField
