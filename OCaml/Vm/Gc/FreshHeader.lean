import OCaml.Vm.Gc.FreshEnqueued

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
  have sizeBound : (allocatorRegs R before 10).toNat < 2^54 := by
    have bound := allocator_size R before
    change (allocatorRegs R before 10).toNat ≤ 18014398509481983 at bound
    omega
  have sizeEq : (allocatorRegs R before 10).toNat = size := by
    change (sizeWord (word before (R 10 - 8#64).toNat)).toNat = size
    exact (sizeWord_nat _).trans source.2
  have tagEq : (allocatorRegs R before 11).toNat = tag := by
    change (tagWord (word before (R 10 - 8#64).toNat)).toNat = tag
    exact (tagWord_nat _).trans source.1
  have tagBound : (allocatorRegs R before 11).toNat < 256 := by
    rw [tagEq]
    have h := source.1
    have bound := Nat.mod_lt (word before (R 10 - 8#64).toNat).toNat (by decide : 0 < 256)
    omega
  have header := AllocWrapper.header_of_effect wrapperMemory conditions.windows conditions.wrapper
    sizeBound separate tagBound
  simpa only [sizeEq,tagEq,AllocExact.resultHeader,allocatedPayload] using header

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
  have same : word after (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat =
      word (allocatedSnapshot R before) (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat := by
    simp only [word,allocatedSnapshot,post.memory,writeLog_append,bytesT_writeLog_out _ conditions.queue]
  rw [same]
  exact header

/-- The selected payload is a bounded RAM address, so its header subtraction
agrees with the natural-address representation used by mopup. -/
theorem AllocationConditions.header_address {R c} (conditions : AllocationConditions R c) :
    (allocatedPayload R c - BitVec.ofNat 64 Layout.header_bytes).toNat =
      (allocatedPayload R c).toNat - Layout.header_bytes := by
  have bound : (8#64) ≤ allocatedPayload R c := by
    change 8 ≤ (allocatedPayload R c).toNat
    exact Nat.le_trans (by decide) conditions.wrapper.freeList.nextRead.lower
  simpa only [Layout.header_bytes,show (8#64).toNat = 8 from rfl] using BitVec.toNat_sub_of_le bound

/-- Header agreement in mopup's natural-address interface. -/
theorem Enqueued.header_nat {R qs pl before after size tag} (post : Enqueued R qs pl before after)
    (allocation : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (conditions : HeaderConditions R qs before) :
    HeaderOk (word after ((allocatedPayload R before).toNat - Layout.header_bytes)) size tag := by
  simpa only [allocation.header_address] using post.header allocation source conditions

end OCaml.Vm.Gc.Fresh
