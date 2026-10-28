import OCaml.Vm.Sim.OutListAdapter
import OCaml.Vm.Gc.F1Runtime

/-! Selected listing entry at the concrete F1 layout. -/
namespace OCaml.Vm.Sim.OutListWalk
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives
open Gc

/-- A selected protected byte is owned, below the native stack and outside
custom state. The resource word in the domain is excluded explicitly. -/
theorem selected_point {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {e : Nat × Nat} (member : e ∈ namedBlocked chs c)
    {a : Nat} (inside : VsaIris.InExt e a)
    (resource : ¬ VsaIris.InExt (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor, 8) a) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  have cov := h.blocked_covered e member
  have notFoot := cov.notFoot (fun _ hm => h.ready.block_bounds hm) inside
  obtain ⟨owner, owned, lo, hi⟩ := cov
  have bounds := h.ready.block_bounds owned
  have al := inside.1
  have ah := inside.2
  have below : Layout.sym_caml_extra_heap_resources + 8 ≤ DlHeap.heapStart := by decide
  refine ⟨by omega, notFoot, ?_⟩
  rintro (static | res | alloc)
  · have sh := static.2
    dsimp only at sh
    omega
  · exact resource res
  · exact h.customSpace.allocated a alloc e member inside

/-- Fixed non-domain extents exclude the domain's resource accumulator. -/
theorem fixed_resource_apart : ∀ e ∈ f1Covered,
    e.1 ≠ Boot.WhileMinRuntime.domain →
    e.1 + e.2 ≤ Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor ∨
      Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor + 8 ≤ e.1 := by decide

/-- Reuse the selected spatial invariant for a fixed runtime allocation. -/
theorem selected_fixed {H cap chs c} (h : LibHeapAt H cap chs c)
    {e : Nat × Nat} (member : e ∈ f1Covered) (other : e.1 ≠ Boot.WhileMinRuntime.domain)
    {a : Nat} (inside : VsaIris.InExt e a) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_point h (by simp only [namedBlocked, List.mem_append]; exact Or.inl (Or.inl member)) inside
  have apart := fixed_resource_apart e member other
  intro resource
  have lo := inside.1; have hi := inside.2
  have rl := resource.1; have rh := resource.2
  dsimp only at rl rh
  omega

/-- Low payload globals are not the mutable custom resource word. -/
def ListingStatic (a : Nat) : Prop :=
  ∃ x ∈ [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
    Layout.sym_caml_global_data, Layout.sym_main_argv, Layout.sym_oo_last_id,
    Layout.sym_caml_prim_table + Layout.off_prim_contents], x ≤ a ∧ a < x + 8

/-- Concrete static separation is independent of any arbitrary allocator
write frame. Custom table storage is owned by the selected ledger. -/
theorem selected_static {H cap chs c} (h : LibHeapAt H cap chs c) {a : Nat}
    (point : ListingStatic a) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  have facts : a < DlHeap.heapStart ∧ ¬ VsaIris.VsaHeap.allocGlobal a ∧
      ¬ VsaIris.InExt (Layout.sym_caml_extra_heap_resources, 8) a ∧
      ¬ VsaIris.InExt (Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor, 8) a := by
    rcases point with ⟨x, hx, lo, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [VsaIris.VsaHeap.allocGlobal, VsaIris.VsaHeap.InRange, VsaIris.InExt,
        Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
        Layout.sym_caml_global_data, Layout.sym_main_argv, Layout.sym_oo_last_id,
        Layout.sym_caml_prim_table, Layout.off_prim_contents, Layout.sym_caml_extra_heap_resources,
        Boot.WhileMinRuntime.domain, Layout.off_extra_heap_resources_minor, DlHeap.heapStart] at * <;> omega
  refine ⟨Nat.lt_trans facts.1 (by decide : DlHeap.heapStart < DlHeap.heapEnd), ?_, ?_⟩
  · rintro (global | ⟨low, _, _⟩)
    · exact facts.2.1 global
    · omega
  · rintro (static | resource | table | ⟨nonzero, storage⟩)
    · exact facts.2.2.1 static
    · exact facts.2.2.2 resource
    · obtain ⟨e, he, lo, _⟩ := h.custom.table
      have bound := h.ready.block_bounds he
      have := table.1
      omega
    · rcases h.custom.storage with zero | ⟨e, he, lo, _⟩
      · exact nonzero zero
      · have bound := h.ready.block_bounds he
        have := storage.1
        omega

/-- Scalar domain-field separation, factored before the representation proof. -/
theorem selected_domain_word {H cap chs c} (h : LibHeapAt H cap chs c)
    {off a : Nat} (fits : off + 8 ≤ Layout.domainStateBytes)
    (apart : off + 8 ≤ Layout.off_extra_heap_resources_minor ∨
      Layout.off_extra_heap_resources_minor + 8 ≤ off)
    (lo : Boot.WhileMinRuntime.domain + off ≤ a) (hi : a < Boot.WhileMinRuntime.domain + off + 8) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_point h (e := (Boot.WhileMinRuntime.domain, Layout.domainStateBytes))
    (by simp [namedBlocked, f1Covered]) ⟨by omega, by dsimp only; omega⟩
  intro resource
  have rl := resource.1; have rh := resource.2
  dsimp only at rl rh
  omega

/-- Whole-buffer bounds reduce code, stack and primitive slots to one
selected fixed allocation. -/
theorem selected_buffer {H cap chs c} (h : LibHeapAt H cap chs c)
    {base size a : Nat} (member : (base, size) ∈ f1Covered)
    (other : base ≠ Boot.WhileMinRuntime.domain) (lo : base ≤ a) (hi : a < base + size) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a :=
  selected_fixed h member other ⟨lo, hi⟩

/-- Represented heap words live in the two actual selected heap chunks. -/
theorem selected_object {H cap chs c} (h : LibHeapAt H cap chs c)
    {b n a : Nat} (chunks : InHeapChunks (b - 8) (8 * n + 8))
    (inside : (b - 8 ≤ a ∧ a < b - 8 + 8) ∨ (b ≤ a ∧ a < b + 8 * n)) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  rcases chunks with minor | major
  · apply selected_fixed h (e := (minorRegion.lo, minorRegion.hi - minorRegion.lo))
      (by simp [f1Covered]) (by decide)
    rcases inside with header | payload <;> exact ⟨by omega, by dsimp only; omega⟩
  · apply selected_fixed h (e := (majorRegion.lo, majorRegion.hi - majorRegion.lo))
      (by simp [f1Covered]) (by decide)
    rcases inside with header | payload <;> exact ⟨by omega, by dsimp only; omega⟩

/-- A represented record retains separation from both resource accumulators. -/
theorem selected_record {H cap chs c} (h : LibHeapAt H cap chs c)
    {b a : Nat} (member : b ∈ chs) (lo : b ≤ a) (hi : a < b + chanRecordBytes) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_point h (e := (b, chanRecordBytes))
    (by simp only [namedBlocked, List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨b, member, rfl⟩)))
    ⟨lo, hi⟩
  have apart := h.recordsApart b member (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) (by simp [f1Covered])
  intro resource
  have rl := resource.1; have rh := resource.2
  simp only [Layout.off_extra_heap_resources_minor] at rl rh
  simp only [Layout.domainStateBytes] at apart
  have bound : Layout.off_extra_heap_resources_minor + 8 ≤ Layout.domainStateBytes := by decide
  simp only [Layout.off_extra_heap_resources_minor, Layout.domainStateBytes] at bound
  omega

/-- Scalar code-slot bounds inside the startup code allocation. -/
theorem selected_code {H cap chs c} (h : LibHeapAt H cap chs c)
    {base i size a : Nat} (code : base = Boot.WhileMinHeapChunks.codeBufferPayload)
    (bound : i < size) (fits : 4 * size ≤ f1CodeBytes)
    (lo : base + 4 * i ≤ a) (hi : a < base + 4 * i + 4) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_buffer h (base := Boot.WhileMinHeapChunks.codeBufferPayload) (size := f1CodeBytes)
    (by simp [f1Covered]) (by decide)
  all_goals subst base; omega

/-- Scalar saved-stack bounds use the actual represented stack equation. -/
theorem selected_stack {H cap chs c} (h : LibHeapAt H cap chs c)
    {sp high len a : Nat} (highEq : high = Boot.WhileMinEntry.high)
    (stack : sp + 8 * len = high) (fits : 8 * (len + 2) ≤ Layout.stackBytes)
    (lo : sp - 16 ≤ a) (hi : a < sp + 8 * len) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_buffer h (base := Boot.WhileMinEntry.high - Layout.stackBytes) (size := Layout.stackBytes)
    (by simp [f1Covered]) (by decide)
  all_goals subst high
  all_goals have low : Layout.stackBytes ≤ Boot.WhileMinEntry.high := by decide
  all_goals omega

/-- Scalar primitive-slot bounds inside the selected startup table. -/
theorem selected_prims {H cap chs c} (h : LibHeapAt H cap chs c)
    {base : BitVec 64} {i size a : Nat}
    (prims : base = BitVec.ofNat 64 Boot.WhileMinHeapChunks.primTablePayload)
    (bound : i < size) (fits : size ≤ f1PrimCapacity)
    (lo : base.toNat + 8 * i ≤ a) (hi : a < base.toNat + 8 * i + 8) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  apply selected_buffer h (base := Boot.WhileMinHeapChunks.primTablePayload) (size := 8 * f1PrimCapacity)
    (by simp [f1Covered]) (by decide)
  all_goals rw [prims] at lo hi
  all_goals change Boot.WhileMinHeapChunks.primTablePayload + 8 * i ≤ a at lo
  all_goals change a < Boot.WhileMinHeapChunks.primTablePayload + 8 * i + 8 at hi
  all_goals omega

/-- Small ground field checks stay opaque at the payload union's use site. -/
theorem listing_stackHigh_fits : Layout.off_stack_high + 8 ≤ Layout.domainStateBytes := by decide

theorem listing_trapsp_fits : Layout.off_trapsp + 8 ≤ Layout.domainStateBytes := by decide

theorem listing_stackHigh_resource : Layout.off_extra_heap_resources_minor + 8 ≤ Layout.off_stack_high := by decide

theorem listing_trapsp_resource : Layout.off_extra_heap_resources_minor + 8 ≤ Layout.off_trapsp := by decide

/-- Domain readback before dispatching the payload union. -/
theorem selected_domain_at {H cap chs c} (h : LibHeapAt H cap chs c)
    (domain : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain)
    {off a : Nat} (fits : off + 8 ≤ Layout.domainStateBytes)
    (apart : off + 8 ≤ Layout.off_extra_heap_resources_minor ∨ Layout.off_extra_heap_resources_minor + 8 ≤ off)
    (lo : (word c Layout.sym_Caml_state).toNat + off ≤ a)
    (hi : a < (word c Layout.sym_Caml_state).toNat + off + 8) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  rw [domain] at lo hi
  exact selected_domain_word h fits apart lo hi

/-- Code readback uses its real array index, without reducing a representation. -/
theorem selected_code_at {P : Prog} {H cap chs c} (h : LibHeapAt H cap chs c)
    {base a i : Nat} {w : BitVec 32} (code : base = Boot.WhileMinHeapChunks.codeBufferPayload)
    (fits : 4 * P.code.size ≤ f1CodeBytes) (hw : P.code[i]? = some w)
    (lo : base + 4 * i ≤ a) (hi : a < base + 4 * i + 4) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a :=
  selected_code h code (Array.getElem?_eq_some_iff.mp hw).1 fits lo hi

/-- Primitive readback uses its real primitive-table index. -/
theorem selected_prims_at {P : Prog} {H cap chs c} (h : LibHeapAt H cap chs c)
    {base : BitVec 64} {a i : Nat} {name : String}
    (prims : base = BitVec.ofNat 64 Boot.WhileMinHeapChunks.primTablePayload)
    (fits : P.prims.size ≤ f1PrimCapacity) (hn : P.prims[i]? = some name)
    (lo : base.toNat + 8 * i ≤ a) (hi : a < base.toNat + 8 * i + 8) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a :=
  selected_prims h prims (Array.getElem?_eq_some_iff.mp hn).1 fits lo hi

/-- Channel readback selects ownership through its actual represented id. -/
theorem selected_record_at {world : World} {cp : ChanPlace} {H cap c}
    (h : LibHeapAt H cap (placedChannels cp world.chans.length) c)
    {id b a : Nat} {ch : Chan} (hc : world.chans[id]? = some ch) (hp : cp id = some b)
    (lo : b ≤ a) (hi : a < b + chanRecordBytes) :
    a < DlHeap.heapEnd ∧ ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a :=
  selected_record h (mem_placedChannels.mpr ⟨id, (List.getElem?_eq_some_iff.mp hc).1, hp⟩) lo hi

/-- Actual runtime pins and represented stack select a common live ledger
for every payload byte, including the two C_CALL saved slots. -/
theorem listing_payload_of_pins {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high cap : Nat} {H : List (Nat × Nat)}
    (codeFits : 4 * P.code.size ≤ f1CodeBytes)
    (primsFit : P.prims.size ≤ f1PrimCapacity)
    (heapChunks : ∀ l b o, pl.φ l = some b → s.heap.get? l = some o →
      InHeapChunks (b - 8) (8 * o.wosize + 8))
    (h : LibHeapAt H cap (placedChannels cp s.world.chans.length) c)
    (domain : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain)
    (highEq : high = Boot.WhileMinEntry.high)
    (code : pl.codeBase = Boot.WhileMinHeapChunks.codeBufferPayload)
    (prims : word c (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      BitVec.ofNat 64 Boot.WhileMinHeapChunks.primTablePayload)
    (stack : sp + 8 * s.stack.length = high)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∀ a, VmPoint P s c pl cp sp a → a < DlHeap.heapEnd ∧
      ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  intro a point
  apply VmPoint.fold point
  · intro lo hi
    exact selected_static h ⟨_, List.mem_cons_self, lo, hi⟩
  · intro lo hi
    exact selected_domain_at h domain listing_stackHigh_fits (Or.inr listing_stackHigh_resource) lo hi
  · intro lo hi
    exact selected_domain_at h domain listing_trapsp_fits (Or.inr listing_trapsp_resource) lo hi
  · intro x hx lo hi
    exact selected_static h ⟨x, List.mem_cons_of_mem _ hx, lo, hi⟩
  · intro i w hw lo hi
    exact selected_code_at h code codeFits hw lo hi
  · intro lo hi
    exact selected_stack h highEq stack stackFits lo hi
  · intro l b o _ hp ho inside
    exact selected_object h (heapChunks l b o hp ho) inside
  · intro id ch b hc hp lo hi _
    exact selected_record_at h hc hp lo (by simpa only [chanRecordBytes, Nat.add_assoc] using hi)
  · intro i name hn lo hi
    exact selected_prims_at h prims primsFit hn lo hi

/-- Runtime observations supply the scalar pins used in the entry proof. -/
theorem f1_listing_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high cap : Nat} {H : List (Nat × Nat)}
    (ok : f1Runtime c) (g : OCaml.LoopGeometry f1Layout P s c pl cp high)
    (data : VmPayload P s c pl cp sp high)
    (h : LibHeapAt H cap (placedChannels cp s.world.chans.length) c)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∀ a, VmPoint P s c pl cp sp a → a < DlHeap.heapEnd ∧
      ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ CustomFoot c a := by
  have code : pl.codeBase = Boot.WhileMinHeapChunks.codeBufferPayload := by
    rw [← data.codeBase, ok.freeListShape.codeWord]; rfl
  exact listing_payload_of_pins g.nursery.codeFits g.nursery.primsFit g.nursery.heapChunks h (f1_domain ok)
    (data.stackHigh.symm.trans (f1_stackHigh ok)) code ok.freeListShape.primsWord data.stack.1 stackFits

/-- The real F1 setup supplies the formerly overstrong entry field. -/
theorem f1_outList_entry {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs)
    {ra : BitVec 64} {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high domain entry : Nat} {env : BitVec 64}
    (setup : CcallSetupPost ra [s.accu] f1Layout P s pl cp sp high domain entry env c)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∃ H cap, OutListEntryHeap P s c pl cp sp state H cap := by
  have ok := setup.input.runtime
  have g := setup.geometry
  obtain ⟨H, cap, chs, h⟩ := ok.freeListShape.libHeap
  have ids : chs = placedChannels cp s.world.chans.length :=
    OpenChannels.unique h.channels g.nursery.channelsListed
  subst chs
  have domainEq : (word c Layout.sym_Caml_state).toNat = Boot.WhileMinRuntime.domain := f1_domain ok
  have recordSize : recBytes = chanRecordBytes := rfl
  have records : RecordsPlaced H (word c Layout.sym_Caml_state).toNat
      (placedChannels cp s.world.chans.length) := by
    change RecordsPlaced H (word c Layout.sym_Caml_state).toNat (placedChannels cp s.world.chans.length)
    refine ⟨?_, ?_, ?_, ?_, h.recordsDisjoint, h.records⟩
    · intro a ha
      obtain ⟨e, he, lo, hi⟩ := h.records a ha
      have := h.ready.block_bounds he
      omega
    · intro a ha
      obtain ⟨e, he, lo, hi⟩ := h.records a ha
      have := h.ready.block_bounds he
      rw [recordSize]
      omega
    · intro a ha
      exact h.recordsApart a ha (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by simp [f1Covered])
    · intro a ha
      rw [domainEq]
      exact h.recordsApart a ha (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) (by simp [f1Covered])
  refine ⟨H, cap, ⟨ok.freeListShape.customPins, h, records, h.extents _ (by simp [f1Covered]), ?_, ?_, ?_⟩⟩
  · rw [domainEq]
    exact h.extents _ (by simp [f1Covered])
  · rw [domainEq]
    decide
  · intro a point
    obtain ⟨bound, foot, state⟩ := f1_listing_payload ok g setup.input.data h stackFits a point
    exact ⟨bound, foot, fun ha => state (custom.footprint c a ha)⟩

/-- Coverage transports along the actual native return's retained ledger. -/
theorem selected_covered_mono {H H' : List (Nat × Nat)} {e : Nat × Nat}
    (h : Covered H e) (sub : ∀ e ∈ H, e ∈ H') : Covered H' e := by
  obtain ⟨owner, member, lo, hi⟩ := h
  exact ⟨owner, sub owner member, lo, hi⟩

/-- The unchanged remembered-table shape is retargeted to the returned ledger. -/
theorem selected_table_mono {H H' : List (Nat × Nat)} {chs : List Nat} {c : Config}
    (h : RefTableAt H chs c) (sub : ∀ e ∈ H, e ∈ H') : RefTableAt H' chs c := by
  refine ⟨h.pointer, h.minorWsz, ?_⟩
  rcases h.shape with empty | allocated
  · exact Or.inl empty
  · exact Or.inr { allocated with covered := selected_covered_mono allocated.covered sub }

/-- The actual spatial return reconstructs every selected F1 heap field.
Only the numeric reserve at this same returned capacity remains to be supplied
by native allocation spending; no returned LibHeapAt is assumed. -/
structure OutListHeapRestored (H : List (Nat × Nat)) (capacity : Nat) (chs : List Nat) (d : Config) : Prop where
  heap : Boot.Startup.HeapReady H capacity d
  physical : CustomOwned CustomFoot H d
  restore : Gc.reserved (word d (refTable + Layout.off_ref_table_base)).toNat chs.length ≤ capacity →
    LibHeapAt H capacity chs d

/-- Rebuild from the real spatial/custom return and selected unchanged
ref-table/named ledger. The conditional result exposes exactly where a
capacity-spending supplier must connect to the returned heap witness. -/
theorem OutListReturned.restore_heap {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    {w : Walk} {k cap : Nat} {ra s0 : BitVec 64} {c d : Config}
    (custom : CustomMemCall Ready state Customs)
    (ret : OutListReturned w Ready state Customs k ra s0 c d)
    (h : LibHeapAt w.H0 cap w.chs c)
    (keepTable : ∀ y, InTableWords y → (d.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0)
    (keepNamed : ∀ a, NamedRead c a → byte d a = byte c a) :
    ∃ H capacity, OutListHeapRestored H capacity w.chs d := by
  obtain ⟨H, capacity, heapD, physical, ledgerD, spaceD, namedD, sub⟩ :=
    ret.spatial_heap custom h.ready h.customSpace h.named h.blocked_covered keepNamed
  have blocked : namedBlocked w.chs d = namedBlocked w.chs c := by
    simp only [namedBlocked, structWord_keep keepTable (off := Layout.off_ref_table_base) (by decide),
      structWord_keep keepTable (off := Layout.off_ref_table_end) (by decide)]
  refine ⟨H, capacity, ⟨heapD, physical, fun room => ?_⟩⟩
  exact {
    room := room
    channelsBound := h.channelsBound
    ready := heapD
    extents := fun e he => selected_covered_mono (h.extents e he) sub
    channels := ret.opened
    records := fun a ha => selected_covered_mono (h.records a ha) sub
    recordsApart := h.recordsApart
    recordsDisjoint := h.recordsDisjoint
    recordsAligned := h.recordsAligned
    table := selected_table_mono (h.table.congr keepTable) sub
    tableIn := sub _ h.tableIn
    named := blocked ▸ namedD
    custom := ledgerD
    customSpace := blocked ▸ spaceD
    customRecords := h.customRecords }

/-- Every physical named read is protected by the actual setup's payload
frame, even if its named representation uses a different logical placement. -/
theorem outList_named_frame {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry k cap : Nat} {env ra s0 : BitVec 64} {c d : Config} {w : Walk}
    (setup : CcallSetupPost ra [s.accu] L P s pl cp sp high domain entry env c)
    (ent : OutListEntry Ready state Customs ra P s pl cp sp c w k cap s0)
    (ret : OutListReturned w Ready state Customs k ra s0 c d)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∀ a, NamedRead c a → byte d a = byte c a := by
  have stack := setup.input.data.stack.1
  have statics := setup.geometry.statics
  obtain ⟨misses, _⟩ := outW_payload setup.geometry ent stack (by omega) (by omega)
  have frame := outW_frame ent.geometry ret
  intro a read
  obtain ⟨other, names, chains, represented, foot⟩ := read
  obtain ⟨chains', represented'⟩ := setup.input.data.named
  exact frame a (misses.named a ((represented.foot_eq represented' a).mp foot))

end OCaml.Vm.Sim.OutListWalk
