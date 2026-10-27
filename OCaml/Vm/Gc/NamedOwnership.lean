import OCaml.Vm.Gc.F1Heap
import OCaml.Vm.Boot.Startup.DomainRecord
import OCaml.Vm.Primitives.MemoryFrame

/-! Named nodes occupy their own live malloc blocks, rather than fixed F1
extents. These adapters consume the actual allocation ledger `H`. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris

/-- The actual malloc result supplies ownership for an appended named entry.
The request is arbitrary; this imposes no fixed name-length or table-size bound. -/
theorem NamedOwned.append {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    (owned : OCaml.Vm.NamedOwned H pl named) (count : pl.nodes.length = named.length)
    (key : String) (value : Val) (node requested : Nat) (size : 16 + key.length + 1 ≤ requested) :
    OCaml.Vm.NamedOwned ((node, requested) :: H) {pl with nodes := pl.nodes ++ [node]}
      (named ++ [(key, value)]) := by
  constructor
  intro i k v n hk hn
  change (pl.nodes ++ [node])[i]? = some n at hn
  rcases Nat.lt_or_ge i named.length with old | new
  · rw [List.getElem?_append_left old] at hk
    rw [List.getElem?_append_left (by omega)] at hn
    obtain ⟨bytes, member, fits⟩ := owned.nodes i k v n hk hn
    exact ⟨bytes, List.mem_cons_of_mem _ member, fits⟩
  · rw [List.getElem?_append_right new] at hk
    rw [List.getElem?_append_right (by omega), count] at hn
    have index : i - named.length = 0 := by
      have bound := (List.getElem?_eq_some_iff.mp hk).1
      simp only [List.length_singleton] at bound
      omega
    simp only [index, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk hn
    obtain ⟨rfl, rfl⟩ := hk
    subst n
    exact ⟨requested, List.mem_cons_self, size⟩

/-- Replacing values keeps named allocations when indexed keys and physical
nodes stay the same. This is the found-node producer's ownership frame. -/
theorem NamedOwned.values {H : List (Nat × Nat)} {pl pl' : Place} {named named' : List (String × Val)}
    (owned : OCaml.Vm.NamedOwned H pl named) (nodes : pl'.nodes = pl.nodes)
    (keys : ∀ (i : Nat) (k : String) (v : Val), named'[i]? = some (k, v) → ∃ old, named[i]? = some (k, old)) :
    OCaml.Vm.NamedOwned H pl' named' := by
  constructor
  intro i k v n hk hn
  obtain ⟨old, entry⟩ := keys i k v hk
  rw [nodes] at hn
  exact owned.nodes i k old n entry hn

/-- A physical named read lies below the arena end, using its matching
selected allocation ledger. -/
theorem NamedLedger.read_bounds {H blocked : List (Nat × Nat)} {cap : Nat} {c : Config}
    (ledger : NamedLedger H blocked c) (heap : Boot.Startup.HeapReady H cap c)
    {x : Nat} (read : NamedRead c x) : x < heapEnd := by
  rcases ledger.read_covered read with bucket | ⟨e, he, lo, hi⟩
  · have bound : Layout.sym_named_value_table + 104 ≤ heapEnd := by decide
    omega
  · have bounds := heap.block_bounds he
    omega

/-- Named bytes are outside newlib's footprint for this selected ledger.
`HeapReady` alone, with an arbitrary `H`, does not supply this fact. -/
theorem NamedLedger.read_not_foot {H blocked : List (Nat × Nat)} {cap : Nat} {c : Config}
    (ledger : NamedLedger H blocked c) (heap : Boot.Startup.HeapReady H cap c)
    {x : Nat} (read : NamedRead c x) : ¬ VsaIris.VsaHeap.vsaFoot H x := by
  have cov := ledger.read_covered read
  rintro (global | ⟨lo, hi, unowned⟩)
  · rcases cov with bucket | ⟨e, he, lo, hi⟩
    · unfold VsaIris.VsaHeap.allocGlobal VsaIris.VsaHeap.InRange at global
      simp only [Layout.sym_named_value_table] at bucket
      omega
    · have bounds := heap.block_bounds he
      rcases VsaIris.VsaHeap.allocGlobal_off_arena x global with below | above <;> omega
  · rcases cov with bucket | ⟨e, he, elo, ehi⟩
    · simp only [Layout.sym_named_value_table, heapStart] at *; omega
    · exact unowned e he ⟨elo, by omega⟩

/-- Fresh malloc writes miss the named bytes, including the static buckets.
The ownership premise is supplied by the represented allocation invariant. -/
theorem NamedOwned.fresh {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    {p n : Nat} (owned : OCaml.Vm.NamedOwned H pl named)
    (low : heapStart ≤ p) (pos : 0 < n)
    (fresh : ∀ e ∈ H, ∀ y, InExt (p, n) y → ¬ InExt e y) :
    ∀ x, NamedPlFoot pl named x → OutWRange [⟨p, p + n⟩] x 1 := by
  intro x f
  rcases NamedOwned.covered owned f with ⟨lo, hi⟩ | cov
  · have bound : Layout.sym_named_value_table + 104 ≤ heapStart := by decide
    exact ⟨Or.inl (by dsimp only; omega), trivial⟩
  · have apart := fresh_apart_covered fresh cov (by simp : 0 < (x, 1).2)
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
  rcases NamedOwned.covered owned (table.foot_sub f) with ⟨lo, hi⟩ | ⟨e, member, lo, hi⟩
  · exact buckets x lo hi
  · rw [Primitives.byte_total, Primitives.byte_total]
    exact live.byte e member x ⟨lo, by omega⟩

end OCaml.Vm.Gc
