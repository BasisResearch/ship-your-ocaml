import OCaml.Refinement

/-!
# Collector facts at startup

The free-list invariant is a named parameter, to be supplied by the
collector proof. All machine addresses come from the generated layout.
`PromotedRuntimeOk` records the empty-nursery requirement in the A0 brief;
it must not be confused with promotion of just the global-data root.
-/

namespace OCaml.Vm

open Vsa.Machine

/-- A small first-order projection, suitable for checking trace candidates
without reducing an entire Sail state in the kernel. -/
structure RuntimeFields where
  youngStart : Nat
  youngEnd : Nat
  allocStart : Nat
  allocEnd : Nat
  youngPtr : Nat
  youngLimit : Nat
  somethingToDo : Nat
  deriving Repr, DecidableEq

/-- Read a domain field through the generated `Caml_state` symbol. -/
def domainWord (c : Config) (offset : Nat) : Nat :=
  (word c ((word c Layout.sym_Caml_state).toNat + offset)).toNat

/-- The concrete collector projection for the pinned ELF. -/
def runtimeFields (c : Config) : RuntimeFields where
  youngStart := domainWord c Layout.off_young_start
  youngEnd := domainWord c Layout.off_young_end
  allocStart := domainWord c Layout.off_young_alloc_start
  allocEnd := domainWord c Layout.off_young_alloc_end
  youngPtr := domainWord c Layout.off_young_ptr
  youngLimit := domainWord c Layout.off_young_limit
  somethingToDo := (word32 c Layout.sym_caml_something_to_do).toNat

/-- Bounds for the downward-growing minor heap, in bytes. -/
structure MinorHeapBounds (r : RuntimeFields) : Prop where
  nonempty : r.youngStart < r.youngEnd
  start : r.youngStart ≤ r.allocStart
  alloc : r.allocStart ≤ r.youngPtr
  ptr : r.youngPtr ≤ r.allocEnd
  stop : r.allocEnd ≤ r.youngEnd
  limitLow : r.allocStart ≤ r.youngLimit
  limitHigh : r.youngLimit ≤ r.allocEnd
  alignedStart : r.allocStart % 8 = 0
  alignedEnd : r.allocEnd % 8 = 0
  alignedPtr : r.youngPtr % 8 = 0

/-- Runtime invariant for the requested post-collection cut. The allocator
and collector summaries must supply `freeList`; it is not assumed true. -/
structure PromotedRuntimeOk (freeList : Config → Prop) (c : Config) : Prop where
  bounds : MinorHeapBounds (runtimeFields c)
  emptyMinor : (runtimeFields c).youngPtr = (runtimeFields c).allocEnd
  noPending : (runtimeFields c).somethingToDo = 0
  freeListShape : freeList c

/-- A concrete `Layout.runtimeOk`, parameterized only by the free-list shape. -/
def promotedLayout (freeList : Config → Prop) : OCaml.Layout :=
  ⟨PromotedRuntimeOk freeList⟩

/-- A nonempty observed nursery rules out the requested invariant once the
machine-to-projection equality is certified. The equality is a genuine open
boot obligation, not a theorem about the untrusted emulator trace. -/
theorem not_promotedRuntimeOk_of_projection {freeList : Config → Prop}
    {c : Config} {r : RuntimeFields} (projection : runtimeFields c = r)
    (nonempty : r.youngPtr ≠ r.allocEnd) : ¬ PromotedRuntimeOk freeList c := by
  intro h
  exact nonempty (projection ▸ h.emptyMinor)

end OCaml.Vm
