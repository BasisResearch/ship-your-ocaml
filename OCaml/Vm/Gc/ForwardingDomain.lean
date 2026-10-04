import OCaml.Vm.Gc.ForwardingComplete

namespace OCaml.Vm.Gc.ForwardingTable
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- Published sources belong to the original finite source set. Combined
with Complete, the table domain is exactly the forwarded subset of that set. -/
def Bounded (copies : List PendingCopy) (sources : List (BitVec 64)) : Prop :=
  ∀ q ∈ copies, q.source ∈ sources

theorem Bounded.extend {copies sources q} (bounded : Bounded copies sources) (member : q.source ∈ sources) :
    Bounded (q :: copies) sources := by
  intro p hp
  rcases List.mem_cons.mp hp with same | hp
  · subst p; exact member
  · exact bounded p hp

theorem identity_of_absent {copies a} (absent : ∀ q ∈ copies, q.source.toNat ≠ a) :
    relocation copies a = a := by
  have missing : copies.find? (fun q => q.source.toNat == a) = none := by
    apply List.find?_eq_none.mpr
    intro q member equal
    exact absent q member (by simpa using equal)
  simp only [relocation,missing,Option.map_none,Option.getD_none]

/-- The partial relocation fixes every address outside its source set. -/
theorem Bounded.identity {copies sources source} (bounded : Bounded copies sources)
    (outside : source ∉ sources) : relocation copies source.toNat = source.toNat := by
  apply identity_of_absent
  intro q member equal
  have same : q.source = source := BitVec.eq_of_toNat_eq equal
  exact outside (same ▸ bounded q member)

/-- A fresh nonzero header has not yet acquired a partial-map entry. -/
theorem fresh_identity {copies pl c source} (view : (eqv copies).P pl 0 c)
    (fresh : word c (source - 8#64).toNat ≠ 0) : relocation copies source.toNat = source.toNat := by
  apply identity_of_absent
  intro q member equal
  exact fresh_source view fresh q member (BitVec.eq_of_toNat_eq equal)

/-- Table coverage plus its domain bound characterize the published subset
by the actual zero headers, independently of entry order or repetition. -/
theorem domain_iff {copies sources pl c source} (view : (eqv copies).P pl 0 c)
    (bounded : Bounded copies sources) (complete : Complete sources copies c) :
    (∃ q ∈ copies, q.source = source) ↔ source ∈ sources ∧ word c (source - 8#64).toNat = 0 := by
  constructor
  · rintro ⟨q,member,equal⟩
    exact ⟨equal ▸ bounded q member,equal ▸ (view q member).1⟩
  · rintro ⟨member,zero⟩
    exact complete source member zero

/-- A represented base pointer outside the collected sources retains its
word under the resulting placement, including old-generation pointers. -/
theorem Bounded.pointer_fixed {copies sources pl source l}
    (bounded : Bounded copies sources) (outside : source ∉ sources)
    (placed : pl.φ l = some source.toNat) :
    relocWord (relocation copies) pl (.ptr l 0) source = source := by
  simp only [relocWord,placed,bounded.identity outside,Nat.mul_zero,Nat.add_zero,
    BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- Actual nursery rejection supplies source-set exclusion when the heap
invariant locates every collected source strictly inside those bounds. -/
theorem Bounded.nonYoung_fixed {copies sources pl source l lo hi}
    (bounded : Bounded copies sources) (inside : ∀ q ∈ sources, lo < q.toNat ∧ q.toNat < hi)
    (outside : ¬ (lo < source.toNat ∧ source.toNat < hi)) (placed : pl.φ l = some source.toNat) :
    relocWord (relocation copies) pl (.ptr l 0) source = source :=
  bounded.pointer_fixed (fun member => outside (inside source member)) placed

end OCaml.Vm.Gc.ForwardingTable
