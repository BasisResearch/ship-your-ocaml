import OCaml.Vm.Repr

/-! Finite primitive-table certificates with small, independently checked rows. -/
namespace OCaml.Vm.Boot
open OCaml.Bytecode Vsa.Machine

structure PrimitiveRow where
  name : String
  entry : Nat

/-- One concrete row agrees with both PRIM and the executable's resolver. -/
structure PrimitiveRowAt (P : Prog) (c : Config) (i : Nat) (r : PrimitiveRow) : Prop where
  program : P.prims[i]? = some r.name
  resolver : PrimitiveEntries.lookup r.name = some r.entry
  target : primitiveTarget c i = BitVec.ofNat 64 r.entry

/-- Convert a row certificate to the production primitive-binding interface. -/
theorem PrimitiveRowAt.binding {P : Prog} {c : Config} {i : Nat} {r : PrimitiveRow}
    (h : PrimitiveRowAt P c i r) {name : String} (hp : P.prims[i]? = some name) :
    ∃ entry, PrimitiveEntries.lookup name = some entry ∧ primitiveTarget c i = BitVec.ofNat 64 entry := by
  have hn : r.name = name := Option.some.inj (h.program.symm.trans hp)
  exact ⟨r.entry, hn ▸ h.resolver, h.target⟩

end OCaml.Vm.Boot
