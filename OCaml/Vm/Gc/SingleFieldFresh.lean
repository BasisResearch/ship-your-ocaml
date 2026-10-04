import OCaml.Vm.Gc.SingleFieldYoung
import OCaml.Vm.Gc.ContextAllocated

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Actual header word encountered by the captured child after parent forwarding. -/
def childHeader (q : PendingCopy) (root : BitVec 64) (c : Config) : BitVec 64 :=
  word (forwardedSnapshot q root c) (child q root c - 8#64).toNat

def childAllocatorRegs (q : PendingCopy) (root sp : BitVec 64) (c : Config) :=
  Fresh.contextRegs (child q root c) q.target sp (childHeader q root c)

/-- A fresh scanned child's typed header and allocator observations in the
concrete post-forwarding snapshot. Heap ownership must supply these facts. -/
structure FreshChildHeader (q : PendingCopy) (root sp : BitVec 64) (size tag : Nat) (c : Config) : Prop where
  headerRead : ReadWindow (child q root c - 8#64) 8
  header : HeaderOk (childHeader q root c) size tag
  positive : 0 < size
  scanned : tag < 249

structure FreshChildConditions (q : PendingCopy) (root sp : BitVec 64) (size tag : Nat) (c : Config) : Prop
    extends FreshChildHeader q root sp size tag c where
  allocation : Fresh.ContextAllocationConditions (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)

theorem YoungHead.context_carried {q root sp before after} (head : YoungHead q root sp before after) :
    GHolds after.σ (Fresh.contextCarried sp q.target) :=
  (gholds_append _ _).mpr ⟨⟨head.stack,head.target,True.intro⟩,head.constants⟩

/-- The captured child and actual prologue constants supply the fresh header
classifier's register interface. Header facts come from the current snapshot. -/
theorem YoungHead.fresh_input {q root sp size tag before after}
    (head : YoungHead q root sp before after) (conditions : FreshChildHeader q root sp size tag before) :
    Fresh.Input (child q root before) after := by
  have memory : after.σ.mem = (forwardedSnapshot q root before).σ.mem := head.memory
  obtain ⟨nonzero,scanned⟩ := Fresh.header_conditions conditions.header conditions.positive conditions.scanned
  refine ⟨head.good,head.minstret,head.tick,head.code,
    ⟨head.value,gholds_lookup _ head.constants rfl,True.intro⟩,conditions.headerRead,?_,?_⟩
  · simpa only [childHeader,word,memory] using nonzero
  · simpa only [childHeader,word,memory] using scanned

/-- Shared exact-log and native-frame composition after any allocation of
the captured child. This retains the parent's already-executed prefix. -/
theorem YoungHead.complete_allocation {q root sp hd payload log writes before middle after}
    (head : YoungHead q root sp before middle)
    (allocated : Fresh.ContextAllocated (child q root before) q.target sp hd payload log middle after writes) :
    Fresh.ContextAllocated (child q root before) q.target sp hd payload
      (Enqueue.prefixLog q.source q.target root ++ log) before after ([8,9,14,15,25] ++ writes) := by
  refine ⟨allocated.good,allocated.minstret,allocated.tick,allocated.code,allocated.pc,
    allocated.registers,allocated.stack,allocated.constants,?_,allocated.output.trans head.output,?_⟩
  · rw [allocated.memory,head.memory,writeLog_append]
  · intro r noise outside
    exact (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (head.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

/-- Result after forwarding the parent and allocating its captured child. -/
abbrev ChildAllocated (q : PendingCopy) (root sp : BitVec 64) (before after : Config) :=
  Fresh.ContextAllocated (child q root before) q.target sp (childHeader q root before)
    (Fresh.contextPayload (child q root before) q.target sp (childHeader q root before) (forwardedSnapshot q root before))
    (Enqueue.prefixLog q.source q.target root ++
      AllocWrapper.effect (childAllocatorRegs q root sp before) (forwardedSnapshot q root before)) before after
    ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15]))

/-- Tail-process a fresh young child through its real exact-size allocation.
The resulting source/destination registers describe the child, while the
existing native frame is unchanged and the log retains the parent prefix. -/
theorem YoungHead.allocate_child {q root sp size tag before middle}
    (head : YoungHead q root sp before middle) (conditions : FreshChildConditions q root sp size tag before) :
    FnSummary Fresh.pc (fun d => d = middle)
      (ChildAllocated q root sp before) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := head.memory
  have headerSame : word middle (child q root before - 8#64).toNat = childHeader q root before := by
    simp only [childHeader,word,memory]
  have allocation : Fresh.ContextAllocationConditions
      (Fresh.contextRegs (child q root before) q.target sp (word middle (child q root before - 8#64).toNat)) middle := by
    rw [headerSame]
    exact conditions.allocation.of_memory memory
  apply (Fresh.allocate_context (head.fresh_input conditions.toFreshChildHeader) head.context_carried allocation).weaken (fun _ h => h)
  intro after allocated
  rw [headerSame,Fresh.contextPayload_of_memory memory,AllocWrapper.effect_of_memory memory] at allocated
  exact head.complete_allocation allocated

/-- Concrete parent forwarding through fresh-child allocation on the same
frame, ready for the next forwarding/copy iteration. -/
theorem prepare_allocate_child {q root sp domain size tag c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c)
    (conditions : FreshChildConditions q root sp size tag c) :
    FnSummary pc (fun d => d = c) (ChildAllocated q root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_young input stack constants even range).run
  intro middle head
  have pc : PCAt Fresh.pc middle := by
    simpa only [OldifyYoung.exitPc,Fresh.pc] using head.pc
  exact (head.allocate_child conditions).run middle ⟨pc,rfl⟩

end OCaml.Vm.Gc.SingleField
