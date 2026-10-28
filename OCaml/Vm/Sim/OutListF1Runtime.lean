import OCaml.Vm.Sim.OutListF1
import OCaml.Vm.Gc.CustomMemCredit

/-! Actual listing-return reconstruction. The remaining numeric reserve is
indexed by the capacity of the real selected native return, never inferred
from allocator write framing or spatial ownership. -/
namespace OCaml.Vm.Sim.OutListWalk
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm OCaml.Vm.Primitives Gc

/-- Small certificates describe the existing concrete runtime read windows. -/
theorem listing_kept_bounds : ∀ v ∈ keptFootprint, v.hi ≤ DlHeap.heapEnd := by decide

theorem listing_kept_minor : ∀ v ∈ keptFootprint,
    v.hi ≤ minorRegion.lo ∨ minorRegion.hi ≤ v.lo := by decide

theorem listing_kept_young : ∀ v ∈ keptFootprint,
    v.hi ≤ f1Domain + 8 ∨ f1Domain + 16 ≤ v.lo := by decide

theorem listing_kept_roots : ∀ v ∈ keptFootprint,
    v.hi ≤ f1Domain + Layout.off_local_roots ∨ f1Domain + Layout.off_local_roots + 8 ≤ v.lo := by decide

theorem listing_kept_resource : ∀ v ∈ keptFootprint,
    v.hi ≤ Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor ∨
      Boot.WhileMinRuntime.domain + Layout.off_extra_heap_resources_minor + 8 ≤ v.lo := by decide

theorem listing_dynamic_covered : ∀ v ∈ dynamicKept,
    ∃ e ∈ f1Covered, e.1 ≤ v.lo ∧ v.hi ≤ e.1 + e.2 := by decide

/-- Bytes in the kept footprint retain the same containing read window. -/
theorem listing_kept_byte {x n j : Nat} (inside : InKept x n) (bound : j < n) : InKept (x + j) 1 := by
  obtain ⟨v, member, lo, hi⟩ := inside
  exact ⟨v, member, by omega, by omega⟩

/-- Static kept reads miss every ignored mutable word. -/
theorem listing_static_misses {a : Nat} {v : W} (member : v ∈ staticKept)
    (lo : v.lo ≤ a) (hi : a < v.hi) {w : W} (ignored : w ∈ ignoredStatics) :
    a < w.lo ∨ w.hi ≤ a := by
  have apart := staticKept_apart v member w ignored
  omega

/-- The selected ledger protects actual runtime reads from both allocator
metadata writes and mutable custom state. -/
theorem listing_kept_owned {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs) {H cap chs c}
    (h : LibHeapAt H cap chs c) {a : Nat} (inside : InKept a 1) :
    ¬ VsaIris.VsaHeap.vsaFoot H a ∧ ¬ state c a := by
  obtain ⟨v, member, lo, hi⟩ := inside
  rcases List.mem_append.mp member with static | dynamic
  · have high := staticKept_below v static
    have low : Layout.sym_bss_end ≤ DlHeap.heapStart := by decide
    constructor
    · rintro (global | ⟨arena, _, _⟩)
      · obtain ⟨w, hw, wl, wh⟩ := allocGlobal_ignored global
        have := listing_static_misses static lo (by omega) hw
        omega
      · omega
    · intro stateA
      have resource := (custom.apart c a stateA).static (by omega)
      have miss := listing_static_misses static lo (by omega)
        (show ⟨Layout.sym_caml_extra_heap_resources, Layout.sym_caml_extra_heap_resources + 8⟩ ∈ ignoredStatics by
          simp [ignoredStatics])
      have rl := resource.1; have rh := resource.2
      dsimp only at rl rh miss
      omega
  · obtain ⟨e, he, elo, ehi⟩ := listing_dynamic_covered v dynamic
    have resource := listing_kept_resource v (List.mem_append.mpr (Or.inr dynamic))
    have safety := selected_point h
      (e := e) (by simp only [namedBlocked, List.mem_append]; exact Or.inl (Or.inl he))
      (a := a) ⟨by omega, by omega⟩ (by
        intro r
        have rl := r.1; have rh := r.2
        dsimp only at rl rh
        omega)
    exact ⟨safety.2.1, fun ha => safety.2.2 (custom.footprint c a ha)⟩

/-- Actual open records miss the runtime's kept bytes. -/
theorem listing_kept_record {H cap chs c} (h : LibHeapAt H cap chs c)
    {a r : Nat} (inside : InKept a 1) (record : r ∈ chs) : a < r + 64 ∨ r + 68 ≤ a := by
  obtain ⟨v, member, lo, hi⟩ := inside
  rcases List.mem_append.mp member with static | dynamic
  · have high := staticKept_below v static
    obtain ⟨e, he, elo, ehi⟩ := h.records r record
    have bounds := h.ready.block_bounds he
    have low : Layout.sym_bss_end ≤ DlHeap.heapStart := by decide
    omega
  · obtain ⟨e, he, elo, ehi⟩ := listing_dynamic_covered v dynamic
    have apart := h.recordsApart r record e he
    have big : 68 ≤ chanRecordBytes := by decide
    omega

/-- The real listing footprint misses kept reads, except the young-limit word
whose actual returned value is used separately below. -/
theorem listing_core_misses {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs) {H cap chs c}
    (h : LibHeapAt H cap chs c) (domain : (word c Layout.sym_Caml_state).toNat = f1Domain)
    (minorLow : minorRegion.lo ≤ (runtimeFields c).youngLimit)
    (minorHigh : (runtimeFields c).youngPtr ≤ minorRegion.hi)
    {a : Nat} (inside : InKept a 1) (limit : a < f1Domain ∨ f1Domain + 8 ≤ a) :
    ¬ OutListWrites state H chs c a := by
  have point := inside
  obtain ⟨v, member, lo, hi⟩ := inside
  have bounds := listing_kept_bounds v member
  have minor := listing_kept_minor v member
  have young := listing_kept_young v member
  have roots := listing_kept_roots v member
  obtain ⟨foot, stateA⟩ := listing_kept_owned custom h point
  rintro (native | nursery | ⟨r, hr, rl, rh⟩ | dom | rootsWrite | state | alloc)
  · omega
  · omega
  · have := listing_kept_record h point hr
    omega
  · rw [domain] at dom
    omega
  · rw [domain] at rootsWrite
    omega
  · exact stateA state
  · exact foot alloc

/-- Reconstruct kept runtime words from actual returned memory, using the
native limit readback instead of pretending the synthetic limit store misses it. -/
theorem outList_core_frame {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high k cap : Nat}
    {ra s0 : BitVec 64} {c d : Config} {w : Walk}
    (ok : f1Runtime c) (g : OCaml.LoopGeometry f1Layout P s c pl cp high)
    (ent : OutListEntry Ready state Customs ra P s pl cp sp c w k cap s0)
    (ret : OutListReturned w Ready state Customs k ra s0 c d) :
    ∀ x n, InKept x n → bytesT d.σ.mem x n = bytesT c.σ.mem x n := by
  have domain := f1_domain ok
  have wd : w.D = f1Domain := ent.domain.trans domain
  have limit : bytesT d.σ.mem f1Domain 8 = bytesT c.σ.mem f1Domain 8 := by
    change word d f1Domain = word c f1Domain
    have returned := ret.limit
    have initial := ent.input.limit
    simpa only [wd, Layout.off_young_limit, Nat.add_zero] using returned.trans initial.symm
  intro x n inside
  apply Reloc.bytesT_congr
  intro j hj
  by_cases word : f1Domain ≤ x + j ∧ x + j < f1Domain + 8
  · have same := byte_of_bytesT limit (i := x + j - f1Domain) (by omega)
    have address : f1Domain + (x + j - f1Domain) = x + j := by omega
    rw [address] at same
    simp only [bytesT, same]
  · exact outW_frame ent.geometry ret _ fun writes =>
      listing_core_misses custom ent.selected domain g.nursery.nurseryLow g.nursery.nurseryHigh
        (listing_kept_byte inside hj) (by omega)
        (by rw [ent.chs]; exact outW_writes ent writes)

/-- The two domain fields read by remembered-table geometry are outside
all listing stores and custom resource writes. -/
theorem listing_table_domain_fields :
    ∀ off ∈ [Layout.off_ref_table, Layout.off_minor_heap_wsz],
      off + 8 ≤ Layout.domainStateBytes ∧ 16 ≤ off ∧
      (off + 8 ≤ 288 ∨ 296 ≤ off) ∧
      (off + 8 ≤ Layout.off_extra_heap_resources_minor ∨ Layout.off_extra_heap_resources_minor + 8 ≤ off) := by decide

theorem listing_table_numeric : refTable + 56 ≤ minorRegion.lo ∧
    f1Domain + Layout.domainStateBytes ≤ refTable ∧ refTable + 56 ≤ DlHeap.heapEnd ∧
    Layout.off_local_roots + 8 ≤ Layout.domainStateBytes ∧ 16 ≤ Layout.domainStateBytes := by decide

/-- Actual returned memory keeps the selected remembered-table words;
custom allocated storage is separated by the full selected spatial ledger. -/
theorem outList_table_frame {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp k cap : Nat}
    {ra s0 : BitVec 64} {c d : Config} {w : Walk}
    (ok : f1Runtime c)
    (ent : OutListEntry Ready state Customs ra P s pl cp sp c w k cap s0)
    (ret : OutListReturned w Ready state Customs k ra s0 c d) :
    ∀ a, InTableWords a → (d.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 := by
  have domain := f1_domain ok
  have wd : w.D = f1Domain := ent.domain.trans domain
  have field : ∀ off ∈ [Layout.off_ref_table, Layout.off_minor_heap_wsz], ∀ a,
      f1Domain + off ≤ a → a < f1Domain + off + 8 → ¬ outW w state a := by
    intro off member a lo hi
    obtain ⟨fits, young, roots, extra⟩ := listing_table_domain_fields off member
    have address : a = w.D + off + (a - (f1Domain + off)) := by rw [wd]; omega
    rw [address]
    exact domainField_not_outW custom ent.geometry (by omega) fits young roots extra
  intro a table
  have frame := outW_frame ent.geometry ret
  have outside : ¬ outW w state a := by
    rcases table with pointer | structPoint | wsz
    · exact field _ (by simp) a pointer.1 pointer.2
    · intro writes
      have written := outW_writes ent writes
      have safe := selected_fixed ent.selected (e := (refTable, 56)) (by simp [f1Covered]) (by decide) structPoint
      have nums := listing_table_numeric
      have low := ent.geometry.nurseryLow
      have high := ent.geometry.nurseryHigh
      have initialLimit := ent.limit
      have initialYoung := ent.young
      have rl := structPoint.1; have rh := structPoint.2
      have recordSize : 68 ≤ chanRecordBytes := by decide
      rcases written with native | nursery | ⟨r, hr, rlo, rhi⟩ | dom | roots | state | alloc
      · omega
      · omega
      · rw [← ent.chs] at hr
        have apart := ent.selected.recordsApart r hr (refTable, 56) (by simp [f1Covered])
        dsimp only at apart
        omega
      · rw [domain] at dom; omega
      · rw [domain] at roots; omega
      · exact safe.2.2 (custom.footprint c a state)
      · exact safe.2.1 alloc
    · exact field _ (by simp) a wsz.1 wsz.2
  have equality := frame a outside
  rw [byte_total, byte_total] at equality
  exact equality

/-- Every ordinary runtime field is rebuilt at the checked native return.
The caller supplies only a separately reconstructed selected allocator heap. -/
theorem outList_runtime_fields {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace} {sp high k cap : Nat}
    {ra s0 : BitVec 64} {c d : Config} {w : Walk}
    (ok : f1Runtime c) (g : OCaml.LoopGeometry f1Layout P s c pl cp high)
    (ent : OutListEntry Ready state Customs ra P s pl cp sp c w k cap s0)
    (ret : OutListReturned w Ready state Customs k ra s0 c d)
    (heap : LibHeap d) : f1Runtime d := by
  obtain ⟨pins, fields⟩ := f1_core (outList_core_frame custom ok g ent ret) (fun _ => heap) ok.freeListShape
  have wd : w.D = f1Domain := ent.domain.trans (f1_domain ok)
  have young := ret.young
  have geometry := ent.geometry
  have room := geometry.room
  have listed : (listedRecs c.σ.mem w.chs).length = (outChannelIds s.world).length := by
    rw [ent.listed, List.length_map]
  rw [wd] at young
  have youngNat : (word d (f1Domain + Layout.off_young_ptr)).toNat =
      w.Y - 48 * (listedRecs c.σ.mem w.chs).length := by
    rw [young, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have high := geometry.nurseryHigh
    have bound : minorRegion.hi < 2 ^ 64 := by decide
    omega
  have pending : (runtimeFields d).somethingToDo = 0 := by
    rw [fields]; exact ok.noPending
  refine { bounds := ?_, noPending := pending, freeListShape := pins }
  rw [fields]
  have bounds := ok.bounds
  rw [youngNat, listed]
  have old := ent.young
  have lim := ent.limit
  have aligned := geometry.youngAligned
  exact {
    nonempty := bounds.nonempty
    start := bounds.start
    alloc := by
      change (runtimeFields c).allocStart ≤ w.Y - 48 * (outChannelIds s.world).length
      have low := bounds.limitLow
      omega
    ptr := by
      change w.Y - 48 * (outChannelIds s.world).length ≤ (runtimeFields c).allocEnd
      have high := bounds.ptr
      omega
    stop := bounds.stop
    limitLow := bounds.limitLow
    limitHigh := bounds.limitHigh
    alignedStart := bounds.alignedStart
    alignedEnd := bounds.alignedEnd
    alignedPtr := by
      change (w.Y - 48 * (outChannelIds s.world).length) % 8 = 0
      omega }

/-- The checked native return rebuilds the complete F1 runtime conditional
only on reserve at this selected returned capacity. The capacity condition is
not discharged by HeapReady or by spatial custom ownership. -/
structure OutListF1Restored (H : List (Nat × Nat)) (capacity : Nat) (chs : List Nat) (d : Config) : Prop
    extends OutListHeapRestored H capacity chs d where
  runtime : Gc.reserved (word d (refTable + Layout.off_ref_table_base)).toNat chs.length ≤ capacity →
    f1Runtime d

/-- Concrete listing reconstruction from the real setup, selected entry ledger
and checked returned memory. The missing native component is numeric reserve
for this same existential heap, including actual input credit and spending
through every CustomMemCall. No returned runtime or LibHeapAt is assumed. -/
theorem outList_f1_restore {Ready : Nat → Config → Prop} {state Customs : Config → Nat → Prop}
    (custom : CustomMemCall Ready state Customs)
    {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high domain entry k cap : Nat} {env ra s0 : BitVec 64} {c d : Config} {w : Walk}
    (setup : CcallSetupPost ra [s.accu] f1Layout P s pl cp sp high domain entry env c)
    (ent : OutListEntry Ready state Customs ra P s pl cp sp c w k cap s0)
    (ret : OutListReturned w Ready state Customs k ra s0 c d)
    (stackFits : 8 * (s.stack.length + 2) ≤ Layout.stackBytes) :
    ∃ H capacity, OutListF1Restored H capacity w.chs d := by
  obtain ⟨H, capacity, spatial⟩ := ret.restore_heap custom ent.selected
    (outList_table_frame custom setup.input.runtime ent ret)
    (outList_named_frame setup ent ret stackFits)
  exact ⟨H, capacity, {
    toOutListHeapRestored := spatial
    runtime := fun room => outList_runtime_fields custom setup.input.runtime setup.geometry ent ret
      ⟨H, capacity, w.chs, spatial.restore room⟩ }⟩

end OCaml.Vm.Sim.OutListWalk
