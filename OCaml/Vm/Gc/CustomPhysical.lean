import OCaml.Vm.Gc.ChannelCustomCount
import OCaml.Vm.Gc.CustomMemCredit
import OCaml.Vm.Gc.CustomResources

/-! Complete mutable channel-custom observations. Stable domain/table identity
and call parameters remain in CustomCallPins, with their independent producers.
The native allocation, resource arithmetic, and exact transition remain the
accepted CustomMemCall obligation. Captured memory is not reset execution. -/
namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- All seven table words are physically zero before the first allocation. -/
structure NullCustomTable (c : Config) : Prop where
  words : ∀ off ∈ [Layout.off_custom_table_base, Layout.off_custom_table_ptr,
    Layout.off_custom_table_end, CustomTable.off_threshold, CustomTable.off_limit,
    CustomTable.off_size, CustomTable.off_reserve], word c (customTable + off) = 0

/-- Byte framing of the whole owned table gives every table word. -/
theorem customTableWord_frame {c d : Config}
    (same : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a → byte d a = byte c a)
    {off : Nat} (bound : off + 8 ≤ Layout.custom_table_bytes) :
    word d (customTable + off) = word c (customTable + off) := by
  apply Reloc.bytesT_congr
  intro j hj
  exact same _ ⟨by omega, by dsimp only; omega⟩

/-- Full allocated shape, including the true limit, survives caller frames. -/
theorem CustomTableShape.frame {c d : Config} {n : Nat} (shape : CustomTableShape c n)
    (same : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a → byte d a = byte c a) :
    CustomTableShape d n := by
  have keep := @customTableWord_frame c d same
  obtain ⟨base, end_⟩ := customAddresses_frame same
  exact {
    base := by rw [base]; exact shape.base
    pointer := by rw [keep (off := Layout.off_custom_table_ptr) (by decide), base]; exact shape.pointer
    threshold := by rw [keep (off := CustomTable.off_threshold) (by decide), base]; exact shape.threshold
    limit := by rw [keep (off := CustomTable.off_limit) (by decide), keep (off := CustomTable.off_threshold) (by decide)]; exact shape.limit
    ending := by rw [end_, base]; exact shape.ending
    size := by rw [keep (off := CustomTable.off_size) (by decide)]; exact shape.size
    reserve := by rw [keep (off := CustomTable.off_reserve) (by decide)]; exact shape.reserve }

/-- Caller separation depends on the explicitly framed Caml_state pointer,
not on any unobserved read-only native parameter. -/
theorem CallerApart.congr {c d : Config} {a : Nat} (apart : CallerApart c a)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state) : CallerApart d a := by
  refine { apart with youngPtr := ?_, youngLimit := ?_, localRoots := ?_, domainField := ?_ }
  · simpa only [domainAddr, domain] using apart.youngPtr
  · simpa only [domainAddr, domain] using apart.youngLimit
  · simpa only [domainAddr, domain] using apart.localRoots
  · simpa only [domainAddr, domain] using apart.domainField

/-- The actual null-storage footprint satisfies every existing caller
separation law. All table/static/domain extents are the observed ones. -/
theorem nullCustom_caller {c : Config} (pins : CustomCallPins c) (zero : customBase c = 0) :
    ∀ a, CustomFoot c a → CallerApart c a := by
  intro a foot
  have range : VsaIris.InExt (Layout.sym_caml_extra_heap_resources, 8) a ∨
      VsaIris.InExt (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor, 8) a ∨
      VsaIris.InExt (customTable, Layout.custom_table_bytes) a := by
    rcases foot with static | minor | table | ⟨nonzero, _⟩
    · exact Or.inl static
    · exact Or.inr (Or.inl minor)
    · exact Or.inr (Or.inr table)
    · exact False.elim (nonzero zero)
  have domain : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := by
    rw [pins.domain]; rfl
  have covered : ∀ e ∈ f1Covered, e.1 ≠ Boot.WhileMinRuntime.domain →
      (e.1 + e.2 ≤ Layout.sym_caml_extra_heap_resources ∨ Layout.sym_caml_extra_heap_resources + 8 ≤ e.1) ∧
      (e.1 + e.2 ≤ Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor ∨
        Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor + 8 ≤ e.1) ∧
      (e.1 + e.2 ≤ customTable ∨ customTable + Layout.custom_table_bytes ≤ e.1) := by decide
  constructor
  all_goals
    try simp only [domainAddr, domain, Nat.add_zero]
  case covered =>
    intro e member other inside
    have apart := covered e member other
    have lo := inside.1; have hi := inside.2
    simp only [VsaIris.InExt] at range
    try dsimp only at lo hi
    omega
  case «static» =>
    intro low
    simp only [VsaIris.InExt, customTable, Boot.WhileMinRuntime.customTable,
      Boot.WhileMinRuntime.domain, Layout.off_extra_heap_resources_minor, DlHeap.heapStart] at range low ⊢
    omega
  case domainField =>
    intro inside
    simp only [VsaIris.InExt, customTable, Boot.WhileMinRuntime.customTable,
      Boot.WhileMinRuntime.domain, Layout.off_extra_heap_resources_minor, Layout.domainStateBytes,
      Layout.sym_caml_extra_heap_resources, Layout.custom_table_bytes] at range inside ⊢
    omega
  all_goals
    simp only [VsaIris.InExt, customTable, Boot.WhileMinRuntime.customTable,
      Boot.WhileMinRuntime.domain, Layout.off_extra_heap_resources_minor, Layout.domainStateBytes,
      Layout.sym_caml_extra_heap_resources, Layout.custom_table_bytes, DlHeap.heapEnd,
      minorRegion, Layout.off_young_ptr, Layout.off_young_limit, Layout.off_local_roots] at range ⊢ <;> omega

/-- Mutable physical accounting, independently of model channel refcounts.
Both resource words are exact binary64 targets; the table is either the fully
observed initial zero table or the full allocated quiet shape. -/
structure PhysicalCustoms (c : Config) (n : Nat) : Prop where
  count : ChannelCustomCount c n
  caller : ∀ a, CustomFoot c a → CallerApart c a
  bounded : n ≤ quietBound
  major : word c Layout.sym_caml_extra_heap_resources = BitVec.ofNat 64 (majorResourceBits n)
  minor : word c (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor) =
    BitVec.ofNat 64 (minorResourceBits n)
  table : if n = 0 then NullCustomTable c else CustomTableShape c n

/-- Natural counts stay unique even though resource arithmetic is finite. -/
theorem PhysicalCustoms.unique {c : Config} {n m : Nat}
    (first : PhysicalCustoms c n) (second : PhysicalCustoms c m) : n = m :=
  first.count.unique second.count

/-- All physical accounting reads are in the existing mutable footprint.
Stable call pins are deliberately absent from this frame law. -/
theorem PhysicalCustoms.frame {c d : Config} {n : Nat} (physical : PhysicalCustoms c n)
    (same : ∀ a, CustomFoot c a → byte d a = byte c a)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state) : PhysicalCustoms d n := by
  have table := fun a ha => same a (Or.inr (Or.inr (Or.inl ha)))
  obtain ⟨base, end_⟩ := customAddresses_frame table
  have major : word d Layout.sym_caml_extra_heap_resources = word c Layout.sym_caml_extra_heap_resources :=
    Reloc.bytesT_congr fun j hj => same _ (Or.inl ⟨by omega, by dsimp only; omega⟩)
  have minor : word d (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor) =
      word c (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor) :=
    Reloc.bytesT_congr fun j hj => same _ (Or.inr (Or.inl ⟨by omega, by dsimp only; omega⟩))
  refine ⟨physical.count.frame (fun a ha => table a ?_),
    (fun a foot => (physical.caller a (((customFoot_congr base end_).1 a).mp foot)).congr domain), physical.bounded,
    major.trans physical.major, minor.trans physical.minor, ?_⟩
  · rcases ha with base | ptr <;>
      simp only [customTable, Layout.off_custom_table_base, Layout.off_custom_table_ptr,
        VsaIris.InExt, Layout.custom_table_bytes] at * <;> omega
  · have shape := physical.table
    by_cases zero : n = 0
    · simp only [zero, ↓reduceIte] at shape ⊢
      constructor
      intro off member
      have bound : off + 8 ≤ Layout.custom_table_bytes := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [customTableWord_frame table bound]
      exact shape.words off member
    · simp only [zero, ↓reduceIte] at shape ⊢
      exact shape.frame table

/-- Concrete full physical zero from generated captured total-read certificates. -/
theorem PhysicalCustoms.startup {c : Config}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem Boot.WhileMinImage.initialMem Boot.WhileMinLog.log)) :
    PhysicalCustoms c 0 := by
  have zero : customBase c = 0 := by
    unfold customBase customTable
    rw [Boot.WhileMinRuntime.read_custom_table_base memory]
    rfl
  refine ⟨ChannelCustomCount.startup memory, nullCustom_caller (CustomCallPins.startup memory) zero, by decide,
    Boot.WhileMinRuntime.read_caml_extra_heap_resources memory,
    Boot.WhileMinRuntime.read_extra_heap_resources_minor memory, ?_⟩
  constructor
  intro off member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Boot.WhileMinRuntime.read_custom_table_base memory
  · exact Boot.WhileMinRuntime.read_custom_table_ptr memory
  · exact Boot.WhileMinRuntime.read_custom_table_end memory
  · exact Boot.WhileMinRuntime.read_custom_table_threshold memory
  · exact Boot.WhileMinRuntime.read_custom_table_limit memory
  · exact Boot.WhileMinRuntime.read_custom_table_size memory
  · exact Boot.WhileMinRuntime.read_custom_table_reserve memory

/-- Readiness relates the full physical observations to the remaining count.
Native quiet execution is still a premise, including its arithmetic linkage. -/
def PhysicalReady : Nat → Config → Prop := ReadyOf PhysicalCustoms

/-- The concrete mutable footprint is present only at physically ready
states. This makes caller separation a proved global law without asserting
anything about malformed arbitrary table pointers. -/
def PhysicalState (c : Config) (a : Nat) : Prop :=
  (∃ n, PhysicalCustoms c n) ∧ CustomFoot c a

/-- Real accounting laws frame the actual mutable footprint; external call
pins have their own producers and are not consequences of readiness. -/
theorem physicalAccounting : CustomAccounting PhysicalReady PhysicalState PhysicalCustoms where
  unique := PhysicalCustoms.unique
  frame := fun physical same domain => physical.frame (fun a ha => by
    rw [byte_total, byte_total]; exact same a ⟨⟨_, physical⟩, ha⟩) domain
  ready := fun h => h

/-- Concrete state bytes satisfy the accepted footprint law. -/
theorem physical_footprint (c : Config) (a : Nat) : PhysicalState c a → CustomFoot c a := fun h => h.2

/-- Physical readiness observes the entire existing mutable footprint. -/
theorem physical_complete {k : Nat} {c : Config} (ready : PhysicalReady k c)
    {a : Nat} (foot : CustomFoot c a) : PhysicalState c a := by
  obtain ⟨n, physical, _⟩ := ready
  exact ⟨⟨n, physical⟩, foot⟩

/-- All concrete state bytes have the real caller separation law. -/
theorem physical_apart {c : Config} {a : Nat} (state : PhysicalState c a) : CallerApart c a := by
  obtain ⟨⟨n, physical⟩, foot⟩ := state
  exact physical.caller a foot

/-- The full existing readiness/state frame is proved from actual observations.
Only native execution and its exact returned transition remain unsupplied. -/
theorem physical_frame {k : Nat} {c d : Config} (ready : PhysicalReady k c)
    (same : ∀ a, PhysicalState c a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0)
    (domain : word d Layout.sym_Caml_state = word c Layout.sym_Caml_state) :
    PhysicalReady k d ∧ (∀ a, PhysicalState d a ↔ PhysicalState c a) := by
  obtain ⟨n, physical, bound⟩ := ready
  have keep : ∀ a, CustomFoot c a → byte d a = byte c a := fun a ha => by
    rw [byte_total, byte_total]
    exact same a ⟨⟨n, physical⟩, ha⟩
  have after := physical.frame keep domain
  have addresses := customAddresses_frame (fun a ha => keep a (Or.inr (Or.inr (Or.inl ha))))
  have foot := (customFoot_congr addresses.1 addresses.2).1
  exact ⟨⟨n, after, bound⟩, fun a =>
    ⟨fun h => ⟨⟨n, physical⟩, (foot a).mp h.2⟩,
     fun h => ⟨⟨n, after⟩, (foot a).mpr h.2⟩⟩⟩

/-- Stable observed identity completes the existing allocated table interface. -/
theorem PhysicalCustoms.quietTable {c : Config} {n : Nat} (physical : PhysicalCustoms c n)
    (pins : CustomCallPins c) (positive : n ≠ 0) : QuietCustomTable c n := by
  refine { (by simpa only [positive, ↓reduceIte] using physical.table : CustomTableShape c n) with
    tableWord := pins.table
    nurseryWords := ?_ }
  unfold domainAddr
  rw [pins.domain]
  exact pins.words (Boot.WhileMinRuntime.domain + Layout.off_minor_heap_wsz, 0x40000#64)
    (by simp [customCallWords])

/-- Table growth cannot be ruled out by occupancy alone; the complete pins
and shape above supply the actual no-growth comparison. -/
theorem PhysicalCustoms.not_full {c : Config} {n : Nat} (physical : PhysicalCustoms c n)
    (pins : CustomCallPins c) (positive : n ≠ 0) :
    (word c (customTable + Layout.off_custom_table_ptr)).toNat <
      (word c (customTable + CustomTable.off_limit)).toNat :=
  (physical.quietTable pins positive).not_full physical.bounded

/-- Actual observed table interval bounds, with an unwrapped natural end. -/
structure QuietCustomBounds (c : Config) : Prop where
  base : 0 < customBase c
  pointerLow : customBase c ≤ (word c (customTable + Layout.off_custom_table_ptr)).toNat
  pointerHigh : (word c (customTable + Layout.off_custom_table_ptr)).toNat <
    (word c (customTable + CustomTable.off_limit)).toNat
  limitHigh : (word c (customTable + CustomTable.off_limit)).toNat < customEnd c
  noWrap : customEnd c < 2 ^ 64

/-- The complete physical shape supplies all table bounds, not only occupancy. -/
theorem PhysicalCustoms.table_bounds {c : Config} {n : Nat} (physical : PhysicalCustoms c n)
    (pins : CustomCallPins c) (positive : n ≠ 0) : QuietCustomBounds c := by
  have table := physical.quietTable pins positive
  refine ⟨Nat.pos_of_ne_zero table.base, ?_, table.not_full physical.bounded, ?_, ?_⟩
  · rw [table.pointer]
    omega
  · rw [table.limit, table.threshold, table.ending]
    have size : Layout.custom_elt_size = 24 := rfl
    rw [size]
    omega
  · exact (word c (customTable + Layout.off_custom_table_end)).isLt

end OCaml.Vm.Gc
