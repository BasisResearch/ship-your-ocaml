import OCaml.Vm.Gc.NamedLedger
import VsaIris.Vsa.HeapRoom
import OCaml.Vm.Reloc
import OCaml.Vm.Boot.WhileMinRuntimeReads

/-! Physical custom-state ownership, independent of accounting and quietness.
The fixed G1 table is the one observed at startup. This footprint does not
observe the domain's table pointer; a full physical predicate must pin and
frame that observation separately. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

def customTable : Nat := Boot.WhileMinRuntime.customTable
def customBase (c : Config) : Nat :=
  (word c (customTable + Layout.off_custom_table_base)).toNat
def customEnd (c : Config) : Nat :=
  (word c (customTable + Layout.off_custom_table_end)).toNat

/-- The physical bytes allowed in the existing custom-state footprint. -/
def CustomFoot (c : Config) (a : Nat) : Prop :=
  VsaIris.InExt (Layout.sym_caml_extra_heap_resources, 8) a ∨
  VsaIris.InExt (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor, 8) a ∨
  VsaIris.InExt (customTable, Layout.custom_table_bytes) a ∨
  (customBase c ≠ 0 ∧ VsaIris.InExt (customBase c, customEnd c - customBase c) a)

/-- Ownership of a caller's actual state bytes in its selected ledger. -/
structure CustomOwned (state : Config → Nat → Prop) (H : List (Nat × Nat))
    (c : Config) : Prop where
  bytes : ∀ a, state c a → a < heapStart ∨ Covered H (a, 1)

theorem CustomOwned.mono {state : Config → Nat → Prop} {H H' : List (Nat × Nat)}
    {c : Config} (h : CustomOwned state H c) (sub : ∀ e ∈ H, e ∈ H') :
    CustomOwned state H' c := by
  constructor
  intro a ha
  rcases h.bytes a ha with low | ⟨e, he, lo, hi⟩
  · exact Or.inl low
  · exact Or.inr ⟨e, sub e he, lo, hi⟩

theorem CustomOwned.frame {state : Config → Nat → Prop} {H : List (Nat × Nat)}
    {c d : Config} (h : CustomOwned state H c)
    (same : ∀ a, state d a ↔ state c a) : CustomOwned state H d :=
  ⟨fun a ha => h.bytes a ((same a).mp ha)⟩

/-- A fresh malloc record cannot contain an already owned custom-state byte. -/
theorem CustomOwned.fresh {state : Config → Nat → Prop} {H : List (Nat × Nat)}
    {c : Config} {p n a : Nat} (h : CustomOwned state H c)
    (fresh : VsaIris.FreshBlock VsaIris.VsaHeap.vsaLayoutP H p n)
    (ha : state c a) : ¬ VsaIris.InExt (p, n) a := by
  intro inside
  rcases h.bytes a ha with low | ⟨e, he, lo, hi⟩
  · have lowP : heapStart ≤ p := fresh.lo
    have lowA := inside.1
    omega
  · exact fresh.disjoint e he a inside ⟨lo, by dsimp only at hi; omega⟩

/-- Concrete allocator resources for the fixed G1 table and its current
storage. Kept separately from `f1Covered`, whose extents callers may write. -/
structure CustomLedger (H : List (Nat × Nat)) (c : Config) : Prop where
  domain : Covered H (Boot.WhileMinRuntime.domain, Layout.domainStateBytes)
  table : Covered H (customTable, Layout.custom_table_bytes)
  storage : customBase c = 0 ∨ Covered H (customBase c, customEnd c - customBase c)

theorem CustomLedger.owned {H : List (Nat × Nat)} {c : Config}
    (h : CustomLedger H c) : CustomOwned CustomFoot H c := by
  constructor
  intro a ha
  rcases ha with static | domain | table | ⟨nonzero, storage⟩
  · have high := static.2
    have bound : Layout.sym_caml_extra_heap_resources + 8 ≤ heapStart := by decide
    exact Or.inl (by dsimp only at high; omega)
  · obtain ⟨e, he, lo, hi⟩ := h.domain
    exact Or.inr ⟨e, he, by have := domain.1; dsimp only at *; omega,
      by
        have high := domain.2
        have bound : Layout.off_extra_heap_resources_minor + 8 ≤ Layout.domainStateBytes := by decide
        dsimp only at high hi ⊢
        omega⟩
  · obtain ⟨e, he, lo, hi⟩ := h.table
    exact Or.inr ⟨e, he, by have := table.1; omega, by have := table.2; dsimp only at *; omega⟩
  · rcases h.storage with zero | ⟨e, he, lo, hi⟩
    · exact False.elim (nonzero zero)
    · exact Or.inr ⟨e, he, by have := storage.1; omega, by have := storage.2; dsimp only at *; omega⟩

theorem CustomLedger.congr {H : List (Nat × Nat)} {c d : Config}
    (h : CustomLedger H c) (base : customBase d = customBase c)
    (end_ : customEnd d = customEnd c) : CustomLedger H d :=
  ⟨h.domain, h.table, by simpa only [base, end_] using h.storage⟩

/-- Only the table's addressing words determine its owned storage range. -/
theorem CustomLedger.frame {H : List (Nat × Nat)} {c d : Config}
    (h : CustomLedger H c)
    (keep : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a →
      byte d a = byte c a) : CustomLedger H d := by
  have wordKeep (off : Nat) (bound : off + 8 ≤ Layout.custom_table_bytes) :
      word d (customTable + off) = word c (customTable + off) := by
    apply Reloc.bytesT_congr
    intro j hj
    exact keep _ ⟨by omega, by dsimp only; omega⟩
  exact h.congr (congrArg BitVec.toNat (wordKeep _ (by decide)))
    (congrArg BitVec.toNat (wordKeep _ (by decide)))

theorem CustomLedger.mono {H H' : List (Nat × Nat)} {c : Config}
    (h : CustomLedger H c) (sub : ∀ e ∈ H, e ∈ H') : CustomLedger H' c := by
  have covered {x} : Covered H x → Covered H' x := by
    rintro ⟨e, he, lo, hi⟩
    exact ⟨e, sub e he, lo, hi⟩
  exact ⟨covered h.domain, covered h.table, h.storage.imp id covered⟩

end OCaml.Vm.Gc
