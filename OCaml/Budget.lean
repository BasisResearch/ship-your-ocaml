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

end OCaml
