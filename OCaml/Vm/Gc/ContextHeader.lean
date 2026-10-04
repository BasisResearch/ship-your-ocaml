import OCaml.Vm.Gc.ContextLargeAllocated
import OCaml.Vm.Gc.ContextQueue
import OCaml.Vm.Gc.FreshHeaderCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- The exact-size allocation on an existing frame writes a header with
the original size/tag. Its counter write must be separate from that header. -/
theorem context_header {source root sp hd size tag before after}
    (memory : after.σ.mem = writeLog before.σ.mem
      (AllocWrapper.effect (contextRegs source root sp hd) before))
    (conditions : ContextAllocationConditions (contextRegs source root sp hd) before)
    (header : HeaderOk hd size tag)
    (separate : (contextPayload source root sp hd before - BitVec.ofNat 64 Layout.header_bytes).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (contextPayload source root sp hd before - BitVec.ofNat 64 Layout.header_bytes).toNat) :
    HeaderOk (word after (contextPayload source root sp hd before - BitVec.ofNat 64 Layout.header_bytes).toNat) size tag := by
  rw [AllocWrapper.effect_eq_core] at memory
  exact header_of_typed_wrapper memory conditions.windows
    (conditions.wrapper.freeOutside (11,AllocEntry.tagOffset) (by simp [AllocEntry.saveCells])) header ⟨rfl,rfl⟩ separate

/-- The least-large-block alternative shares the typed wrapper header law. -/
theorem context_large_header {source root sp hd size tag before after}
    (memory : after.σ.mem = writeLog before.σ.mem
      (AllocLargeWrapper.effect (contextRegs source root sp hd) before))
    (conditions : ContextLargeConditions (contextRegs source root sp hd) before)
    (header : HeaderOk hd size tag)
    (separate : (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) before).toNat + 8 ≤ Layout.sym_caml_allocated_words ∨
      Layout.sym_caml_allocated_words + 8 ≤ (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) before).toNat) :
    HeaderOk (word after (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) before).toNat) size tag :=
  header_of_typed_wrapper memory conditions.windows
    (conditions.wrapper.freeOutside (11,AllocEntry.tagOffset) (by simp [AllocEntry.saveCells])) header ⟨rfl,rfl⟩ separate

/-- Queue insertion preserves the allocated typed header under its concrete
suffix footprint. The pending payload remains available separately. -/
theorem ContextQueued.header {source root sp target log qs pl writes before after size tag a}
    (post : ContextQueued source root sp target log qs pl writes before after)
    (header : HeaderOk (word (contextSnapshot log before) a) size tag)
    (outside : OutLRange (contextQueueEffect source target root log qs before) a 8) :
    HeaderOk (word after a) size tag := by
  apply header_of_suffix ?_ header outside
  simp only [contextSnapshot,post.memory,writeLog_append]

/-- Exact-size allocator geometry supplies the natural header address. -/
theorem ContextAllocationConditions.header_address {source root sp hd c}
    (conditions : ContextAllocationConditions (contextRegs source root sp hd) c) :
    (contextPayload source root sp hd c - BitVec.ofNat 64 Layout.header_bytes).toNat =
      (contextPayload source root sp hd c).toNat - Layout.header_bytes := by
  apply header_address_of_lower
  exact Nat.le_trans (by decide) conditions.wrapper.freeList.nextRead.lower

/-- The large allocator's actual header-write window rules out wraparound. -/
theorem ContextLargeConditions.header_address {source root sp hd c}
    (conditions : ContextLargeConditions (contextRegs source root sp hd) c) :
    (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) c).toNat =
      (contextLargePayload source root sp hd c).toNat - Layout.header_bytes := by
  apply header_address_of_upper
  have upper := conditions.wrapper.body.continuation.account.headerWrite.upper
  change (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) c).toNat + 8 ≤ 0x100000000 at upper
  change (AllocLargeWrapper.resultHeader (contextRegs source root sp hd) c).toNat + 8 < 2^64
  omega

end OCaml.Vm.Gc.Fresh
