import OCaml.Vm.Gc.F1Heap
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Primitives.MemoryFrame

/-! Named nodes occupy their own live malloc blocks, rather than fixed F1
extents. These adapters consume the actual allocation ledger `H`. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris

/-- A named footprint byte is static or covered by an actual owned node. -/
theorem NamedOwned.covered {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    (owned : OCaml.Vm.NamedOwned H pl named) {x : Nat} (f : NamedPlFoot pl named x) :
    (Layout.sym_named_value_table ≤ x ∧ x < Layout.sym_named_value_table + 104) ∨ Covered H (x, 1) := by
  rcases f with bucket | ⟨i, k, v, n, hk, hn, lo, hi⟩
  · exact Or.inl bucket
  · obtain ⟨bytes, member, size⟩ := owned.nodes i k v n hk hn
    exact Or.inr ⟨(n, bytes), member, lo, by dsimp only; omega⟩

/-- Fresh malloc writes miss the named bytes, including the static buckets.
The ownership premise is supplied by the represented allocation invariant. -/
theorem NamedOwned.fresh {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    {p n : Nat} (owned : OCaml.Vm.NamedOwned H pl named)
    (low : heapStart ≤ p) (pos : 0 < n)
    (fresh : ∀ e ∈ H, ∀ y, InExt (p, n) y → ¬ InExt e y) :
    ∀ x, NamedPlFoot pl named x → OutWRange [⟨p, p + n⟩] x 1 := by
  intro x f
  rcases owned.covered f with ⟨lo, hi⟩ | cov
  · have bound : Layout.sym_named_value_table + 104 ≤ heapStart := by decide
    exact ⟨Or.inl (by dsimp only; omega), trivial⟩
  · have apart := fresh_apart_covered fresh cov (by decide : 0 < (x, 1).2)
      (n := n) pos (Nat.le_refl _)
    exact ⟨by dsimp only at apart ⊢; omega, trivial⟩

/-- A malloc live-block frame and the static bucket frame preserve the
named table. This consumes the shared allocator `LiveFrame` interface. -/
theorem NamedRepr.frame_owned {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (Nat × List (BitVec 8) × Val)} {c c' : Config}
    (table : OCaml.Vm.NamedRepr c pl named chains) (owned : OCaml.Vm.NamedOwned H pl named)
    (live : Boot.Startup.LiveFrame H c c')
    (buckets : ∀ x, Layout.sym_named_value_table ≤ x → x < Layout.sym_named_value_table + 104 →
      byte c' x = byte c x) : OCaml.Vm.NamedRepr c' pl named chains := by
  apply table.frame
  intro x f
  rcases owned.covered (table.foot_sub f) with ⟨lo, hi⟩ | ⟨e, member, lo, hi⟩
  · exact buckets x lo hi
  · rw [Primitives.byte_total, Primitives.byte_total]
    exact live.byte e member x ⟨lo, by omega⟩

end OCaml.Vm.Gc
