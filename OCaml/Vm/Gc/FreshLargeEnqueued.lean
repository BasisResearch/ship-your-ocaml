import OCaml.Vm.Gc.FreshLargeAllocated
import OCaml.Vm.Gc.FreshQueueCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

abbrev LargeEnqueueConditions (R : Nat → BitVec 64) (qs : List PendingCopy) (pl : Place) (c : Config) :=
  QueueConditions R (largePayload R c)
    (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) qs pl c

abbrev LargeEnqueued (R : Nat → BitVec 64) (qs : List PendingCopy) (pl : Place) (before after : Config) :=
  QueueResult R (largePayload R before)
    (AllocLargeWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) qs pl before after

/-- Complete fresh-object oldify through least-large-block allocation,
forwarding/root/queue stores and original caller return. The shared result
also provides represented grey payload via `QueueResult.payload`. -/
theorem enqueue_fresh_large {R domain size tag c qs pl} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c) (conditions : LargeEnqueueConditions R qs pl c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (LargeEnqueued R qs pl c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh_large input allocation).run
  intro middle allocated
  exact (allocated.enqueue input.entry conditions).run middle ⟨allocated.pc,rfl⟩

end OCaml.Vm.Gc.Fresh
