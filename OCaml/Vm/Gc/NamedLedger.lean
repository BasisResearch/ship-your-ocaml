import OCaml.Vm.Primitives.MemoryFrame
import VsaIris.DlHeap

/-! A physical named-table snapshot shares the allocator's selected ledger.
The snapshot is independent of the abstract VM heap and its placement.
Only the allocation producer may enlarge the ledger. -/
namespace OCaml.Vm
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Two terminated byte strings at the same address have the same length. -/
theorem NamedNode.key_length {c : Config} {pl pl' : Place} {n next next' : Nat}
    {key key' : List (BitVec 8)} {v v' : Val}
    (h : NamedNode c pl n next key v) (h' : NamedNode c pl' n next' key' v') :
    key.length = key'.length := by
  apply Nat.le_antisymm
  · apply Classical.byContradiction; intro no
    have lt : key'.length < key.length := by omega
    have byte := (h.keyBytes key'.length lt).1
    have ne := (h.keyBytes key'.length lt).2
    rw [h'.nul] at byte
    exact ne byte.symm
  · apply Classical.byContradiction; intro no
    have lt : key.length < key'.length := by omega
    have byte := (h'.keyBytes key.length lt).1
    have ne := (h'.keyBytes key.length lt).2
    rw [h.nul] at byte
    exact ne byte.symm

/-- Node addresses and byte extents are determined by the physical chain. -/
theorem NamedChain.shape_eq {c : Config} {pl pl' : Place} {head : Nat}
    {es es' : List (Nat × List (BitVec 8) × Val)}
    (h : NamedChain c pl head es) (h' : NamedChain c pl' head es') :
    es.map (fun e => (e.1, e.2.1.length)) = es'.map (fun e => (e.1, e.2.1.length)) := by
  -- discipline: allow(O5-run-induction) induction on a physical named chain, not a run
  induction h generalizing es' with
  | nil =>
    cases h' with
    | nil => rfl
    | cons node _ => have low := node.low; simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
  | @cons node next key v rest hn tail ih =>
    cases h' with
    | nil => have low := hn.low; simp only [Vsa.Sim.DlHeap.heapStart] at low; omega
    | cons hn' tail' =>
      have same := hn.key_length hn'
      have nextEq := hn.next.symm.trans hn'.next
      cases nextEq
      simp only [List.map_cons, same, ih tail']

/-- An indexed logical entry has exactly its chain's physical node. -/
theorem NamedRepr.foot_complete {c : Config} {pl : Place} {named : List (String × Val)}
    {chains : Nat → List (Nat × List (BitVec 8) × Val)} (h : NamedRepr c pl named chains) {x : Nat}
    (foot : NamedPlFoot pl named x) : NamedReprFoot chains x := by
  rcases foot with bucket | ⟨i, k, v, n, hk, hn, lo, hi⟩
  · exact Or.inl bucket
  · obtain ⟨b, hb, m, key, member, spelled⟩ := (h.entries k v).mp (List.mem_of_getElem? hk)
    obtain ⟨j, placed, entry⟩ := h.nodes b hb _ member
    have keyI : (named.map Prod.fst)[i]? = some k := by rw [List.getElem?_map, hk]; rfl
    have keyJ : (named.map Prod.fst)[j]? = some k := by rw [List.getElem?_map, entry, spelled]; rfl
    have ij : i = j := (h.unique.getElem?_inj (List.getElem?_eq_some_iff.mp keyI).1).mp (keyI.trans keyJ.symm)
    subst j
    rw [hn] at placed
    cases placed
    exact Or.inr ⟨b, hb, _, member, lo, by rw [← strOf_length', spelled]; exact hi⟩

/-- Every representation of the same physical table reads the same bytes. -/
theorem NamedRepr.foot_eq {c : Config} {pl pl' : Place} {named named' : List (String × Val)}
    {chains chains' : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedRepr c pl named chains) (h' : NamedRepr c pl' named' chains') :
    ∀ x, NamedPlFoot pl named x ↔ NamedPlFoot pl' named' x := by
  have sub {pl₁ pl₂ : Place} {ns₁ ns₂ : List (String × Val)}
      {cs₁ cs₂ : Nat → List (Nat × List (BitVec 8) × Val)}
      (a : NamedRepr c pl₁ ns₁ cs₁) (b : NamedRepr c pl₂ ns₂ cs₂) {x : Nat}
      (f : NamedPlFoot pl₁ ns₁ x) : NamedPlFoot pl₂ ns₂ x := by
    rcases a.foot_complete f with bucket | ⟨i, hi, e, he, lo, top⟩
    · exact Or.inl bucket
    · have shape := (a.heads i hi).shape_eq (b.heads i hi)
      have member : (e.1, e.2.1.length) ∈ (cs₂ i).map (fun e => (e.1, e.2.1.length)) := by
        rw [← shape]; exact List.mem_map.mpr ⟨e, he, rfl⟩
      obtain ⟨e', he', same⟩ := List.mem_map.mp member
      have addr : e'.1 = e.1 := congrArg (fun p : Nat × Nat => p.1) same
      have size : e'.2.1.length = e.2.1.length := congrArg (fun p : Nat × Nat => p.2) same
      exact b.foot_sub (Or.inr ⟨i, hi, e', he', by rw [addr]; exact lo, by rw [addr, size]; exact top⟩)
  exact fun x => ⟨sub h h', sub h' h⟩

/-- A byte read by a representation of the physical named table. -/
def NamedRead (c : Config) (x : Nat) : Prop :=
  ∃ pl named chains, NamedRepr c pl named chains ∧ NamedPlFoot pl named x

namespace Gc

/-- `x` lies inside a live block of `H`. -/
def Covered (H : List (Nat × Nat)) (x : Nat × Nat) : Prop :=
  ∃ e ∈ H, e.1 ≤ x.1 ∧ x.1 + x.2 ≤ e.1 + e.2

/-- A named footprint byte is static or covered by an actual owned node. -/
theorem NamedOwned.covered {H : List (Nat × Nat)} {pl : Place} {named : List (String × Val)}
    (owned : OCaml.Vm.NamedOwned H pl named) {x : Nat} (f : NamedPlFoot pl named x) :
    (Layout.sym_named_value_table ≤ x ∧ x < Layout.sym_named_value_table + 104) ∨ Covered H (x, 1) := by
  rcases f with bucket | ⟨i, k, v, n, hk, hn, lo, hi⟩
  · exact Or.inl bucket
  · obtain ⟨bytes, member, size⟩ := owned.nodes i k v n hk hn
    exact Or.inr ⟨(n, bytes), member, lo, by dsimp only; omega⟩


/-- A named snapshot owned by the selected malloc ledger and separated from
other runtime allocations. `blocked` lists the runtime and channel regions. -/
structure NamedLedgerImage (H blocked : List (Nat × Nat)) (c : Config) (pl : Place)
    (named : List (String × Val)) (chains : Nat → List (Nat × List (BitVec 8) × Val)) : Prop where
  repr : NamedRepr c pl named chains
  owned : NamedOwned H pl named
  apart : ∀ x, NamedPlFoot pl named x → ∀ e ∈ blocked, ¬ VsaIris.InExt e x

/-- The runtime remembers a physical snapshot, with its actual allocation ledger. -/
def NamedLedger (H blocked : List (Nat × Nat)) (c : Config) : Prop :=
  ∃ pl named chains, NamedLedgerImage H blocked c pl named chains

/-- A frame keeps the physical table and its matching ledger. -/
theorem NamedLedgerImage.frame {H blocked : List (Nat × Nat)} {c c' : Config} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedLedgerImage H blocked c pl named chains)
    (keep : ∀ x, NamedPlFoot pl named x → byte c' x = byte c x) :
    NamedLedgerImage H blocked c' pl named chains :=
  ⟨h.repr.frame (fun x f => keep x (h.repr.foot_sub f)), h.owned, h.apart⟩

/-- Enlarging the allocator ledger preserves existing named ownership. -/
theorem NamedLedgerImage.mono {H H' blocked blocked' : List (Nat × Nat)} {c : Config} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedLedgerImage H blocked c pl named chains) (sub : ∀ e ∈ H, e ∈ H')
    (apart : ∀ x, NamedPlFoot pl named x → ∀ e ∈ blocked', ¬ VsaIris.InExt e x) :
    NamedLedgerImage H' blocked' c pl named chains :=
  ⟨h.repr, h.owned.mono sub, apart⟩

/-- An owned snapshot covers every dynamic named byte. -/
theorem NamedLedgerImage.covered {H blocked : List (Nat × Nat)} {c : Config} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedLedgerImage H blocked c pl named chains) {x : Nat} (f : NamedPlFoot pl named x) :
    (Layout.sym_named_value_table ≤ x ∧ x < Layout.sym_named_value_table + 104) ∨
      ∃ e ∈ H, e.1 ≤ x ∧ x + 1 ≤ e.1 + e.2 :=
  NamedOwned.covered h.owned f

/-- The represented table uses this runtime ledger, independently of the
snapshot's abstract placement and values. This chooses no arbitrary `H`. -/
theorem NamedLedger.covered {H blocked : List (Nat × Nat)} {c : Config} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedLedger H blocked c) (table : NamedRepr c pl named chains) {x : Nat}
    (f : NamedPlFoot pl named x) :
    (Layout.sym_named_value_table ≤ x ∧ x < Layout.sym_named_value_table + 104) ∨
      ∃ e ∈ H, e.1 ≤ x ∧ x + 1 ≤ e.1 + e.2 := by
  obtain ⟨pl₀, names₀, chains₀, snapshot⟩ := h
  exact snapshot.covered ((table.foot_eq snapshot.repr x).mp f)

/-- Physical separation is likewise shared by every representation. -/
theorem NamedLedger.apart {H blocked : List (Nat × Nat)} {c : Config} {pl : Place}
    {named : List (String × Val)} {chains : Nat → List (Nat × List (BitVec 8) × Val)}
    (h : NamedLedger H blocked c) (table : NamedRepr c pl named chains) {x : Nat}
    (f : NamedPlFoot pl named x) {e : Nat × Nat} (member : e ∈ blocked) : ¬ VsaIris.InExt e x := by
  obtain ⟨pl₀, names₀, chains₀, snapshot⟩ := h
  exact snapshot.apart x ((table.foot_eq snapshot.repr x).mp f) e member

/-- Frame the recorded physical snapshot through its observable bytes. -/
theorem NamedLedger.frame {H blocked : List (Nat × Nat)} {c c' : Config}
    (h : NamedLedger H blocked c) (keep : ∀ x, NamedRead c x → byte c' x = byte c x) :
    NamedLedger H blocked c' := by
  obtain ⟨pl, named, chains, snapshot⟩ := h
  exact ⟨pl, named, chains, snapshot.frame fun x f => keep x ⟨pl, named, chains, snapshot.repr, f⟩⟩

/-- A retained physical snapshot identifies post-frame named reads with the
same entry reads. This uses the selected snapshot, not arbitrary external writes. -/
theorem NamedLedger.read_back {H blocked : List (Nat × Nat)} {c d : Config}
    (h : NamedLedger H blocked c)
    (keep : ∀ x, NamedRead c x → byte d x = byte c x) {x : Nat}
    (read : NamedRead d x) : NamedRead c x := by
  obtain ⟨pl, names, chains, snapshot⟩ := h
  have kept := snapshot.frame (c' := d) fun x f => keep x ⟨pl, names, chains, snapshot.repr, f⟩
  obtain ⟨pl', names', chains', table, foot⟩ := read
  exact ⟨pl, names, chains, snapshot.repr, (table.foot_eq kept.repr x).mp foot⟩

/-- The matching runtime ledger covers any physically named read. -/
theorem NamedLedger.read_covered {H blocked : List (Nat × Nat)} {c : Config}
    (h : NamedLedger H blocked c) {x : Nat} (read : NamedRead c x) :
    (Layout.sym_named_value_table ≤ x ∧ x < Layout.sym_named_value_table + 104) ∨
      ∃ e ∈ H, e.1 ≤ x ∧ x + 1 ≤ e.1 + e.2 := by
  obtain ⟨pl, named, chains, table, foot⟩ := read
  exact h.covered table foot

/-- Physical named reads miss every recorded foreign allocation. -/
theorem NamedLedger.read_apart {H blocked : List (Nat × Nat)} {c : Config}
    (h : NamedLedger H blocked c) {x : Nat} (read : NamedRead c x)
    {e : Nat × Nat} (member : e ∈ blocked) : ¬ VsaIris.InExt e x := by
  obtain ⟨pl, named, chains, table, foot⟩ := read
  exact h.apart table foot member

/-- Monotone extension of the selected ledger does not lose its named nodes. -/
theorem NamedLedger.mono {H H' blocked : List (Nat × Nat)} {c : Config}
    (h : NamedLedger H blocked c) (sub : ∀ e ∈ H, e ∈ H') : NamedLedger H' blocked c := by
  obtain ⟨pl, named, chains, snapshot⟩ := h
  exact ⟨pl, named, chains, snapshot.mono sub snapshot.apart⟩

/-- Reorder or forget foreign regions without changing the selected ledger. -/
theorem NamedLedger.restrict {H blocked blocked' : List (Nat × Nat)} {c : Config}
    (h : NamedLedger H blocked c) (sub : ∀ e ∈ blocked', e ∈ blocked) : NamedLedger H blocked' c := by
  obtain ⟨pl, named, chains, snapshot⟩ := h
  exact ⟨pl, named, chains, snapshot.mono (fun _ he => he) (fun x f e he => snapshot.apart x f e (sub e he))⟩

/-- A fresh allocation extends the selected ledger and remains separate from
every existing named node. The caller supplies its actual malloc frame. -/
theorem NamedLedger.allocate {H blocked : List (Nat × Nat)} {c c' : Config} {p req size : Nat}
    (h : NamedLedger H blocked c) (low : Vsa.Sim.DlHeap.heapStart ≤ p) (small : size ≤ req)
    (fresh : ∀ e ∈ H, ∀ x, VsaIris.InExt (p, req) x → ¬ VsaIris.InExt e x)
    (keep : ∀ x, NamedRead c x → byte c' x = byte c x) :
    NamedLedger ((p, req) :: H) ((p, size) :: blocked) c' := by
  obtain ⟨pl, named, chains, snapshot⟩ := h
  have kept := snapshot.frame (fun x f => keep x ⟨pl, named, chains, snapshot.repr, f⟩)
  refine ⟨pl, named, chains, kept.mono (fun _ he => List.mem_cons_of_mem _ he) ?_⟩
  intro x f e he
  rcases List.mem_cons.mp he with rfl | he
  · intro inside
    rcases snapshot.covered f with bucket | ⟨e, member, lo, hi⟩
    · have bound : Layout.sym_named_value_table + 104 ≤ Vsa.Sim.DlHeap.heapStart := by decide
      obtain ⟨lo, hi⟩ := inside
      dsimp only at lo hi
      omega
    · exact fresh e member x ⟨inside.1, by have := inside.2; dsimp only at *; omega⟩ ⟨lo, by omega⟩
  · exact snapshot.apart x f e he

end Gc
end OCaml.Vm
