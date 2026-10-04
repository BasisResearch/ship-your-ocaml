import OCaml.Vm.Gc.FreshEnqueued
import OCaml.Vm.Gc.FreshHeaderCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- Accounting and queue writes must be disjoint from the allocated header.
These bounds are the remaining allocator ownership/separation supplier. -/
structure HeaderConditions (R : Nat → BitVec 64) (qs : List PendingCopy) (c : Config) : Prop where
  counter : (allocatedPayload R c - BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
    Layout.sym_caml_allocated_words + 8 ≤ (allocatedPayload R c - BitVec.ofNat 64 Layout.header_bytes).toNat
  queue : OutLRange (enqueueEffect R qs c)
    (allocatedPayload R c - BitVec.ofNat 64 Layout.header_bytes).toNat 8

/-- Header preservation for any configuration with the proved allocation
log, independently of its platform/register postcondition. -/
theorem header_of_allocation {R size tag} {before after : Config}
    (memory : after.σ.mem = writeLog before.σ.mem (allocationEffect R before))
    (conditions : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) :
    HeaderOk (word after (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) size tag := by
  have wrapperMemory : after.σ.mem = writeLog (oldifySnapshot R before).σ.mem
      (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) := by
    rw [memory,allocationEffect,writeLog_append]
    rfl
  rw [AllocWrapper.effect_eq_core] at wrapperMemory
  exact header_of_wrapper_effect wrapperMemory conditions.windows
    (conditions.wrapper.freeOutside (11,AllocEntry.tagOffset) (by simp [AllocEntry.saveCells])) source separate

theorem Allocated.header {R before after size tag} (post : Allocated R before after)
    (conditions : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) :
    HeaderOk (word after (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) size tag :=
  header_of_allocation post.memory conditions source separate

/-- The final pending copy retains the original typed size and tag despite
forwarding, root, work-list and native-return operations. -/
theorem Enqueued.header {R qs pl before after size tag} (post : Enqueued R qs pl before after)
    (allocation : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (conditions : HeaderConditions R qs before) :
    HeaderOk (word after (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) size tag := by
  have header : HeaderOk (word (allocatedSnapshot R before)
      (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat) size tag :=
    header_of_allocation (by simp only [allocatedSnapshot]) allocation source conditions.counter
  exact post.toQueue.header header conditions.queue

/-- The selected payload is a bounded RAM address, so its header subtraction
agrees with the natural-address representation used by mopup. -/
theorem AllocationConditions.header_address {R c} (conditions : AllocationConditions R c) :
    (allocatedPayload R c - BitVec.ofNat 64 Layout.header_bytes).toNat =
      (allocatedPayload R c).toNat - Layout.header_bytes := by
  apply header_address_of_lower
  exact Nat.le_trans (by decide) conditions.wrapper.freeList.nextRead.lower

/-- Header agreement in mopup's natural-address interface. -/
theorem Enqueued.header_nat {R qs pl before after size tag} (post : Enqueued R qs pl before after)
    (allocation : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (conditions : HeaderConditions R qs before) :
    HeaderOk (word after ((allocatedPayload R before).toNat - Layout.header_bytes)) size tag := by
  simpa only [allocation.header_address] using post.header allocation source conditions

end OCaml.Vm.Gc.Fresh
