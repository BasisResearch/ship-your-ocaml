import OCaml.Vm.Gc.ContextHeader
import OCaml.Vm.Gc.SingleFieldFreshLarge

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives

/-- The fresh child's allocated header comes from the actual exact-size
wrapper stores, after the parent's forwarding prefix has already executed. -/
theorem ChildAllocated.header {q root sp size tag before after}
    (post : ChildAllocated q root sp before after)
    (fresh : FreshChildConditions q root sp size tag before)
    (separate : (Fresh.contextPayload (child q root before) q.target sp (childHeader q root before) (forwardedSnapshot q root before) -
        BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤
        (Fresh.contextPayload (child q root before) q.target sp (childHeader q root before) (forwardedSnapshot q root before) -
          BitVec.ofNat 64 Layout.header_bytes).toNat) :
    HeaderOk (word after
      (Fresh.contextPayload (child q root before) q.target sp (childHeader q root before) (forwardedSnapshot q root before) -
        BitVec.ofNat 64 Layout.header_bytes).toNat) size tag := by
  apply Fresh.context_header (conditions := fresh.allocation) (header := fresh.header) (separate := separate)
  simpa only [childAllocatorRegs,forwardedSnapshot,writeLog_append] using post.memory

/-- The least-large-block alternative shares the same header meaning and
retains the parent's prefix in its exact memory composition. -/
theorem ChildLargeAllocated.header {q root sp size tag before after}
    (post : ChildLargeAllocated q root sp before after)
    (fresh : LargeFreshChildConditions q root sp size tag before)
    (separate : (AllocLargeWrapper.resultHeader (childAllocatorRegs q root sp before) (forwardedSnapshot q root before)).toNat + 8 ≤
        Layout.sym_caml_allocated_words ∨ Layout.sym_caml_allocated_words + 8 ≤
          (AllocLargeWrapper.resultHeader (childAllocatorRegs q root sp before) (forwardedSnapshot q root before)).toNat) :
    HeaderOk (word after
      (AllocLargeWrapper.resultHeader (childAllocatorRegs q root sp before) (forwardedSnapshot q root before)).toNat) size tag := by
  apply Fresh.context_large_header (conditions := fresh.allocation) (header := fresh.header) (separate := separate)
  simpa only [childAllocatorRegs,forwardedSnapshot,writeLog_append] using post.memory

end OCaml.Vm.Gc.SingleField
