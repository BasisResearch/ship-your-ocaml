import OCaml.Refinement
import OCaml.Vm.RuntimeFields

/-!
# Collector facts at startup

The free-list invariant is a named parameter, to be supplied by the
collector proof. All machine addresses come from the generated layout.
`RuntimeOk` permits allocations remaining in the nursery at the cut;
promotion of the global-data root does not empty the nursery. Live nursery
blocks are covered by the ordinary `HeapRepr` placement.
-/

namespace OCaml.Vm

open Vsa.Machine

/-- Machine-site and OCaml startup proofs use the same generated mailbox. -/
theorem mailbox_layout : Vsa.Sim.tohostAddr = Layout.sym_tohost := rfl

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

/-- Runtime invariant at the second interpreter entry. The allocator
and collector summaries must supply `freeList`; it is not assumed true. -/
structure RuntimeOk (freeList : Config → Prop) (c : Config) : Prop where
  bounds : MinorHeapBounds (runtimeFields c)
  noPending : (runtimeFields c).somethingToDo = 0
  freeListShape : freeList c

/-- A concrete layout, parameterized by the free-list shape and the heap budget. -/
def runtimeLayout (freeList : Config → Prop) (budget : OCaml.Budget) : OCaml.Layout :=
  ⟨RuntimeOk freeList, budget⟩

/-- The startup invariant allows exactly the ordinary allocation interval;
live blocks in its allocated part are handled by `HeapRepr`. -/
theorem RuntimeOk.youngPtr_bounds {freeList : Config → Prop} {c : Config}
    (h : RuntimeOk freeList c) :
    (runtimeFields c).allocStart ≤ (runtimeFields c).youngPtr ∧
    (runtimeFields c).youngPtr ≤ (runtimeFields c).allocEnd :=
  ⟨h.bounds.alloc, h.bounds.ptr⟩

end OCaml.Vm
