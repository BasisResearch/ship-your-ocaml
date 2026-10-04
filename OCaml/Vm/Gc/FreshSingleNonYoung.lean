import OCaml.Vm.Gc.FreshSingle
import OCaml.Vm.Gc.SingleFieldNonYoung

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initial geometry and actual post-forwarding nursery observations for
an even child requiring no recursive oldification. -/
structure NonYoungSingleConditions (R : Nat → BitVec 64) (target domain : BitVec 64)
    (log : List WEntry) (c : Config) : Prop extends SingleGeometry R target log c where
  even : ChildClassify.even (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) = true
  range : SingleField.RangeConditions (queuePending R target) (R 11) domain (queueSnapshot R log c)

/-- Both actual allocators supply the runtime-domain register, so the even
non-young continuation needs no additional machine-register premise. -/
theorem AllocationResult.single_nonYoung {R target domain log c middle}
    (allocated : AllocationResult R target log c middle) (input : OldifyEntry.Input R c)
    (conditions : NonYoungSingleConditions R target domain log c) :
    FnSummary Enqueue.pc (fun d => d = middle) (SingleResult R target log c) := by
  constructor
  intro start pre
  rcases pre with ⟨_,equal⟩
  subst start
  have memory : middle.σ.mem = (queueSnapshot R log c).σ.mem := by
    simpa only [queueSnapshot] using allocated.memory
  have even : ChildClassify.even (SingleField.child (queuePending R target) (R 11) middle) = true := by
    simpa only [SingleField.child_of_memory memory] using conditions.even
  obtain ⟨after,run,returned⟩ := (SingleField.return_even_nonYoung
    (allocated.single_input conditions.toSingleGeometry) allocated.stack allocated.domainRegister even
    (conditions.range.of_memory memory) (allocated.single_geometry input conditions.toSingleGeometry)).run middle ⟨allocated.pc,rfl⟩
  exact ⟨after,run,allocated.complete_single input conditions.allocationOutside returned⟩

/-- Whole fresh oldify through exact-size allocation, actual even-child
nursery rejection and original caller return, with represented-data interface. -/
theorem single_fresh_nonYoung {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : NonYoungSingleConditions R (allocatedPayload R c) childDomain
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (SingleResult R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh input allocation).run
  intro middle allocated
  exact (allocated.toResult.single_nonYoung input.entry conditions).run middle ⟨allocated.pc,rfl⟩

/-- Whole fresh non-young single-field route after least-large-block allocation. -/
theorem single_fresh_large_nonYoung {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : NonYoungSingleConditions R (largePayload R c) childDomain
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (SingleResult R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh_large input allocation).run
  intro middle allocated
  exact (allocated.single_nonYoung input.entry conditions).run middle ⟨allocated.pc,rfl⟩

end OCaml.Vm.Gc.Fresh
