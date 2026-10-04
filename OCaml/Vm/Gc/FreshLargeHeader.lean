import OCaml.Vm.Gc.FreshLargeEnqueued
import OCaml.Vm.Gc.FreshHeaderCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

def largeHeader (R : Nat → BitVec 64) (c : Config) :=
  AllocLargeWrapper.resultHeader (allocatorRegs R c) (oldifySnapshot R c)

/-- Allocator-counter and queue stores are disjoint from the new header;
collector ownership must supply these finite footprint facts. -/
structure LargeHeaderConditions (R : Nat → BitVec 64) (qs : List PendingCopy) (c : Config) : Prop where
  counter : (largeHeader R c).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
    Layout.sym_caml_allocated_words + 8 ≤ (largeHeader R c).toNat
  queue : OutLRange (queueEffect R (largePayload R c)
    (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) qs c) (largeHeader R c).toNat 8

theorem header_of_large_allocation {R size tag before after}
    (memory : after.σ.mem = writeLog before.σ.mem (largeAllocationEffect R before))
    (conditions : LargeAllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : (largeHeader R before).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (largeHeader R before).toNat) :
    HeaderOk (word after (largeHeader R before).toNat) size tag := by
  have wrapperMemory : after.σ.mem = writeLog (oldifySnapshot R before).σ.mem
      (AllocLargeWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) := by
    rw [memory,largeAllocationEffect,writeLog_append]
    rfl
  exact header_of_wrapper_effect wrapperMemory conditions.windows
    (conditions.wrapper.freeOutside (11,AllocEntry.tagOffset) (by simp [AllocEntry.saveCells])) source separate

theorem LargeEnqueued.header {R qs pl before after size tag} (post : LargeEnqueued R qs pl before after)
    (allocation : LargeAllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (conditions : LargeHeaderConditions R qs before) :
    HeaderOk (word after (largeHeader R before).toNat) size tag := by
  apply QueueResult.header post (hp := largeHeader R before) _ conditions.queue
  exact header_of_large_allocation (by simp only [queueSnapshot,largeAllocationEffect]) allocation source conditions.counter

/-- The actual header write window rules out wraparound when forming the
payload address, supplying mopup's natural-address header interface. -/
theorem LargeAllocationConditions.header_address {R c} (conditions : LargeAllocationConditions R c) :
    (largeHeader R c).toNat = (largePayload R c).toNat - Layout.header_bytes := by
  apply header_address_of_upper
  have upper := conditions.wrapper.body.continuation.account.headerWrite.upper
  change (largeHeader R c).toNat + 8 ≤ 0x100000000 at upper
  change (largeHeader R c).toNat + 8 < 2^64
  omega

theorem LargeEnqueued.header_nat {R qs pl before after size tag} (post : LargeEnqueued R qs pl before after)
    (allocation : LargeAllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (conditions : LargeHeaderConditions R qs before) :
    HeaderOk (word after ((largePayload R before).toNat - Layout.header_bytes)) size tag := by
  simpa only [allocation.header_address] using post.header allocation source conditions

end OCaml.Vm.Gc.Fresh
