/-!
# The resource budget

Low in the import graph so that runtime invariants that relate a `BcSem`
state to the machine through the budget (`Gc.G1Room`) can be stated below
`OCaml/Refinement.lean`.
-/

namespace OCaml

/-- Resource budget. -/
structure Budget where
  stackWords : Nat
  heapWords : Nat
  /-- Custom blocks charged to `caml_extra_heap_resources` (`World.customs`,
  the channels' `refs`). Under G1 the 6th since program start requests a
  major slice (a6-gc's `quietBound`), so the G1 budget bounds them here, like
  the no-collection nursery bound `heapWords`. It is not a `BcSem` guard:
  the compiler differential runs `boot/ocamlc` on `BcSem`, and ocamlc makes
  more custom allocations than that (the three std channels, the source's
  `open_in`, each `.cmi` it reads, the `.cmo`'s `open_out_bin`), so a guard
  would make that run `.unsupported`. -/
  customs : Nat

end OCaml
