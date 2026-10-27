import OCaml.Vm.Sim.Invariant

/-! The old geometry does not separate named nodes from `Caml_state`.
This witnesses the missing fact needed by the field case of `LogWindows`.
It is an obstruction to that geometry-only frame, not a reachable VM state. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def namedAliasState (s : St) : St :=
  { s with world := { s.world with named := [("", .int 0)] } }

def namedAliasAddr (c : Config) : Nat :=
  (word c Layout.sym_Caml_state).toNat + Layout.off_extern_sp

def namedAliasPlace (pl : Place) (c : Config) : Place :=
  { pl with nodes := [namedAliasAddr c] }

/-- A legal old stack geometry whose named node overlaps an allowed domain store. -/
structure NamedDomainAlias (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) (high : Nat) : Prop where
  geometry : OldStackGeometry P (namedAliasState s) c (namedAliasPlace pl c) cp high
  footprint : NamedPlFoot (namedAliasPlace pl c) (namedAliasState s).world.named (namedAliasAddr c)
  clobbers : ¬ OutLRange [(namedAliasAddr c, 8, 0)] (namedAliasAddr c) 1

/-- Keeping the old stack geometry cannot justify a named-memory frame
for a write to `extern_sp`: nodes can still alias that field. A producer must
supply physical separation in the invariant before the generic frame works. -/
theorem StackGeometry.named_domain_alias {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {high : Nat} (g : OldStackGeometry P s c pl cp high) :
    NamedDomainAlias P s c pl cp high := by
  constructor
  · refine { g with
      even := ⟨g.even.code, g.even.heap, g.even.atoms⟩
      words := ⟨g.words.code, g.words.heap, g.words.atoms⟩
      named := ?_ }
    intro a f
    rcases f with bucket | ⟨i, k, v, n, hk, hn, lo, hi⟩
    · have st := g.statics
      have static : Layout.sym_named_value_table + 104 ≤ Layout.sym_bss_end := by decide
      exact ⟨Or.inl (by simp only [stackWindow] at *; omega), trivial⟩
    · have i0 : i = 0 := by
        have := (List.getElem?_eq_some_iff.1 hk).1
        change i < 1 at this
        omega
      subst i
      simp only [namedAliasState, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp only [namedAliasPlace, List.getElem?_cons_zero, Option.some.injEq] at hn
      subst n
      have fits : Layout.off_extern_sp + 17 ≤ Layout.domainStateBytes := by decide
      obtain ⟨apart, _⟩ := g.domain
      exact ⟨by simp only [namedAliasAddr, stackWindow, String.length_empty] at *; omega, trivial⟩
  · exact Or.inr ⟨0, "", .int 0, namedAliasAddr c, rfl, rfl, Nat.le_refl _, by simp; omega⟩
  · intro outside
    have overlap := outside.1
    change namedAliasAddr c + 1 ≤ namedAliasAddr c ∨
      namedAliasAddr c + 8 ≤ namedAliasAddr c at overlap
    omega

/-- The strengthened geometry excludes every domain-field alias. -/
theorem StackGeometry.named_domain_disjoint {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {high off : Nat} (g : StackGeometry P s c pl cp high)
    (fits : off < Layout.domainStateBytes) :
    ¬ NamedPlFoot pl s.world.named ((word c Layout.sym_Caml_state).toNat + off) := by
  intro f
  have apart := (g.domainNamed _ f).1
  dsimp only at apart
  omega

end OCaml.Vm.Sim
