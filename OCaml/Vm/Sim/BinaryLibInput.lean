import OCaml.Vm.Primitives.Leaf

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Library entry obligations. Startup register initialization supplies the
scratch-register witnesses; the caller supplies operands and return address. -/
structure BinaryLibInput (x y ra : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c where
  left : gpr c 10 = some x
  right : gpr c 11 = some y
  scratch2 : ∃ v, gpr c 12 = some v
  scratch3 : ∃ v, gpr c 13 = some v

/-- Defined scratch registers required by the copied libgcc specification.
Startup's register initialization supplies these; dispatch preserves them. -/
structure BinaryLibScratch (c : Config) : Prop where
  a2 : ∃ v, gpr c 12 = some v
  a3 : ∃ v, gpr c 13 = some v

end OCaml.Vm.Sim
