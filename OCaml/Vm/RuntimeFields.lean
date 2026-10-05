import OCaml.Vm.Repr

/-! The collector's scalar runtime fields, read through the generated
`Caml_state` symbol. Kept below `OCaml/Refinement.lean` so that loop-head
invariants (`NurseryGeometry`) can mention them. -/

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

end OCaml.Vm
