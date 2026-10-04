import OCaml.Vm.Gc.FreshSingleData
import OCaml.Vm.Gc.FreshHeader
import OCaml.Vm.Gc.FreshLargeHeader

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- The single-field forwarding and child store preserve a disjoint new
header, using the same suffix-frame rule as queue insertion. -/
theorem SingleResult.header {R target log before after size tag} {hp : BitVec 64}
    (post : SingleResult R target log before after)
    (header : HeaderOk (word (queueSnapshot R log before) hp.toNat) size tag)
    (outside : OutLRange (singleEffect R target log before) hp.toNat 8) :
    HeaderOk (word after hp.toNat) size tag := by
  apply header_of_suffix ?_ header outside
  simp only [queueSnapshot,post.memory,writeLog_append]

theorem single_exact_header {R before after size tag}
    (post : SingleResult R (allocatedPayload R before)
      (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before after)
    (allocation : AllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat)
    (outside : OutLRange (singleEffect R (allocatedPayload R before)
      (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before)
      (allocatedPayload R before - BitVec.ofNat 64 Layout.header_bytes).toNat 8) :
    HeaderOk (word after ((allocatedPayload R before).toNat - Layout.header_bytes)) size tag := by
  have header := post.header
    (header_of_allocation (by simp only [queueSnapshot,allocationEffect]) allocation source separate) outside
  simpa only [allocation.header_address] using header

theorem single_large_header {R before after size tag}
    (post : SingleResult R (largePayload R before)
      (AllocLargeWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before after)
    (allocation : LargeAllocationConditions R before)
    (source : HeaderOk (word before (R 10 - 8#64).toNat) size tag)
    (separate : (largeHeader R before).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (largeHeader R before).toNat)
    (outside : OutLRange (singleEffect R (largePayload R before)
      (AllocLargeWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before) (largeHeader R before).toNat 8) :
    HeaderOk (word after ((largePayload R before).toNat - Layout.header_bytes)) size tag := by
  have header := post.header
    (header_of_large_allocation (by simp only [queueSnapshot,largeAllocationEffect]) allocation source separate) outside
  simpa only [allocation.header_address] using header

end OCaml.Vm.Gc.Fresh
