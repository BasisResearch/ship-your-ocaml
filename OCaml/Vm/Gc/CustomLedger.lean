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

/-- The allocated table struct and its live backing storage. Resource
accumulators are excluded because one intentionally lives in the domain. -/
def CustomAllocFoot (c : Config) (a : Nat) : Prop :=
  VsaIris.InExt (customTable, Layout.custom_table_bytes) a ∨
  (customBase c ≠ 0 ∧ VsaIris.InExt (customBase c, customEnd c - customBase c) a)

/-- Spatial evidence at the selected heap snapshot. `blocked` consists of
actual owned caller regions; named reads are tied to its retained NamedLedger.
This is not a law of arbitrary linked lists or arbitrary external table writes. -/
structure CustomSpace (blocked : List (Nat × Nat)) (c : Config) : Prop where
  allocated : ∀ a, CustomAllocFoot c a → ∀ e ∈ blocked, ¬ VsaIris.InExt e a
  named : ∀ a, CustomFoot c a → ¬ NamedRead c a

/-- Reading the same table addressing words preserves the physical footprint. -/
theorem customFoot_congr {c d : Config}
    (base : customBase d = customBase c) (end_ : customEnd d = customEnd c) :
    (∀ a, CustomFoot d a ↔ CustomFoot c a) ∧
      (∀ a, CustomAllocFoot d a ↔ CustomAllocFoot c a) := by
  simp only [CustomFoot, CustomAllocFoot, base, end_, iff_self, implies_true, and_self]

/-- Forgetting protected extents retains local spatial evidence. -/
theorem CustomSpace.restrict {blocked blocked' : List (Nat × Nat)} {c : Config}
    (h : CustomSpace blocked c) (sub : ∀ e ∈ blocked', e ∈ blocked) : CustomSpace blocked' c :=
  ⟨fun a ha e he => h.allocated a ha e (sub e he), h.named⟩

/-- Spatial transport requires both the table addressing words and a retained
named snapshot. An outside-write custom accounting frame alone is insufficient. -/
theorem CustomSpace.frame {H blocked roots : List (Nat × Nat)} {c d : Config}
    (h : CustomSpace blocked c) (named : NamedLedger H roots c)
    (keepNamed : ∀ a, NamedRead c a → byte d a = byte c a)
    (base : customBase d = customBase c) (end_ : customEnd d = customEnd c) :
    CustomSpace blocked d := by
  obtain ⟨foot, alloc⟩ := customFoot_congr base end_
  exact ⟨fun a ha => h.allocated a ((alloc a).mp ha),
    fun a ha read => h.named a ((foot a).mp ha) (named.read_back keepNamed read)⟩

/-- Owned live bytes cannot be allocator free/metadata bytes. Bounds come
from the same selected ledger's actual heap readiness. -/
theorem Covered.notFoot {H : List (Nat × Nat)} {e : Nat × Nat}
    (covered : Covered H e)
    (bounds : ∀ owner ∈ H, heapStart ≤ owner.1 ∧ owner.1 + owner.2 ≤ heapEnd)
    {a : Nat} (inside : VsaIris.InExt e a) : ¬ VsaIris.VsaHeap.vsaFoot H a := by
  obtain ⟨owner, member, lo, hi⟩ := covered
  have bound := bounds owner member
  have alo := inside.1
  have ahi := inside.2
  rintro (global | ⟨_, _, outside⟩)
  · rcases VsaIris.VsaHeap.allocGlobal_off_arena a global with low | high <;> omega
  · exact outside owner member ⟨by omega, by omega⟩

/-- Growth into an identified free footprint preserves local spatial
separation when actual owned live extents and named reads miss that footprint.
The native callee supplies the growth relation; this lemma proves preservation. -/
theorem CustomSpace.grow {H blocked roots : List (Nat × Nat)} {c d : Config}
    {free : Nat → Prop} (h : CustomSpace blocked c) (named : NamedLedger H roots c)
    (keepNamed : ∀ a, NamedRead c a → byte d a = byte c a)
    (growth : ∀ a, CustomAllocFoot d a → CustomAllocFoot c a ∨ free a)
    (regionApart : ∀ e ∈ blocked, ∀ a, VsaIris.InExt e a → ¬ free a)
    (namedProtected : ∀ a, NamedRead c a → ¬ free a) : CustomSpace blocked d := by
  constructor
  · intro a ha e he inside
    rcases growth a ha with old | fresh
    · exact h.allocated a old e he inside
    · exact regionApart e he a inside fresh
  · intro a ha read
    have oldRead := named.read_back keepNamed read
    rcases ha with static | resource | alloc
    · exact h.named a (Or.inl static) oldRead
    · exact h.named a (Or.inr (Or.inl resource)) oldRead
    · rcases growth a alloc with old | fresh
      · exact h.named a (Or.inr (Or.inr old)) oldRead
      · exact namedProtected a oldRead fresh

/-- Initial spatial evidence from null custom storage, empty actual named
buckets, and the fixed table's checked extent separation. -/
theorem CustomSpace.of_empty {blocked : List (Nat × Nat)} {c : Config}
    (zero : customBase c = 0)
    (buckets : ∀ b, b < 13 → word c (Layout.sym_named_value_table + 8 * b) = 0)
    (apart : ∀ e ∈ blocked, customTable + Layout.custom_table_bytes ≤ e.1 ∨
      e.1 + e.2 ≤ customTable) : CustomSpace blocked c := by
  constructor
  · intro a ha e he inside
    rcases ha with table | ⟨nonzero, _⟩
    · have sep := apart e he
      have lo := table.1
      have hi := table.2
      have elo := inside.1
      have ehi := inside.2
      dsimp only at *
      omega
    · exact nonzero zero
  · intro a ha read
    obtain ⟨pl, names, chains, table, foot⟩ := read
    have empty := NamedRepr.empty c pl buckets
    have bucket := NamedPlFoot.empty.mp ((table.foot_eq empty a).mp foot)
    rcases ha with static | resource | fixed | ⟨nonzero, _⟩
    · have bounds : Layout.sym_caml_extra_heap_resources + 8 ≤ Layout.sym_named_value_table ∨
        Layout.sym_named_value_table + 104 ≤ Layout.sym_caml_extra_heap_resources := by decide
      have lo := static.1
      have hi := static.2
      dsimp only at lo hi
      omega
    · have bounds : Layout.sym_named_value_table + 104 ≤
        Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor := by decide
      have lo := resource.1
      omega
    · have bounds : Layout.sym_named_value_table + 104 ≤ customTable := by decide
      have lo := fixed.1
      omega
    · exact nonzero zero

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

/-- A real fresh allocation extends the protected extents. The pre-state
custom bytes and named snapshot are owned by that same selected H. -/
theorem CustomSpace.allocate {H blocked : List (Nat × Nat)} {c : Config}
    {p req size : Nat} (h : CustomSpace blocked c) (owned : CustomOwned CustomFoot H c)
    (fresh : VsaIris.FreshBlock VsaIris.VsaHeap.vsaLayoutP H p req)
    (small : size ≤ req) : CustomSpace ((p, size) :: blocked) c := by
  refine ⟨?_, h.named⟩
  intro a ha e he
  rcases List.mem_cons.mp he with rfl | he
  · intro inside
    have foot : CustomFoot c a := Or.inr (Or.inr ha)
    exact owned.fresh fresh foot ⟨inside.1, by have := inside.2; dsimp only at *; omega⟩
  · exact h.allocated a ha e he

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

/-- The table's addressing words survive a byte frame on its owned struct. -/
theorem customAddresses_frame {c d : Config}
    (keep : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a →
      byte d a = byte c a) : customBase d = customBase c ∧ customEnd d = customEnd c := by
  have wordKeep (off : Nat) (bound : off + 8 ≤ Layout.custom_table_bytes) :
      word d (customTable + off) = word c (customTable + off) := by
    apply Reloc.bytesT_congr
    intro j hj
    exact keep _ ⟨by omega, by dsimp only; omega⟩
  exact ⟨congrArg BitVec.toNat (wordKeep _ (by decide)),
    congrArg BitVec.toNat (wordKeep _ (by decide))⟩

/-- Only the table's addressing words determine its owned storage range. -/
theorem CustomLedger.frame {H : List (Nat × Nat)} {c d : Config}
    (h : CustomLedger H c)
    (keep : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a →
      byte d a = byte c a) : CustomLedger H d := by
  obtain ⟨base, end_⟩ := customAddresses_frame keep
  exact h.congr base end_

theorem CustomLedger.mono {H H' : List (Nat × Nat)} {c : Config}
    (h : CustomLedger H c) (sub : ∀ e ∈ H, e ∈ H') : CustomLedger H' c := by
  have covered {x} : Covered H x → Covered H' x := by
    rintro ⟨e, he, lo, hi⟩
    exact ⟨e, sub e he, lo, hi⟩
  exact ⟨covered h.domain, covered h.table, h.storage.imp id covered⟩

end OCaml.Vm.Gc
