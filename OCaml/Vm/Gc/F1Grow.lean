import OCaml.Vm.Gc.F1Barrier
import OCaml.Vm.Gc.BarrierGrow
import OCaml.Vm.Sim.ReallocRefTableImage
import OCaml.Vm.Sim.ReallocGenericImage

/-!
# The remembered set's growth from an F1 state

`f1_grow`: at an F1 state whose remembered set is unallocated, the growth
call's precondition `Barrier.Grow` holds over the heap invariant's live blocks.
The readiness comes from `LibHeapAt.ready` and the call's platform facts; the
room is the table's reservation (`tableCharge`); the request is sized by the
pinned `minor_heap_wsz`; the code is the pinned image; the slot lies in a
heap chunk, a live block apart from the struct and `minor_heap_wsz`.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup VsaIris VsaIris.Inst VsaIris.VsaHeap Boot

/-- **The growth call's precondition at an F1 state.** -/
theorem f1_grow {c : Config} {ra sp slot v : BitVec 64} (ok : f1Runtime c)
    (leaf : LeafInput ra c) (platform : VsaOk startupLive c)
    (gp : gprGet c.σ 3 = some VsaIris.MallocFast.gpV) (stack : gprGet c.σ 2 = some sp)
    (frame : NativeFrame sp (32 + (64 + allocHeadroom)))
    (empty : (word c (refTable + Layout.off_ref_table_base)).toNat = 0)
    (slotChunks : InHeapChunks (slot + BitVec.ofNat 64 0).toNat 8) :
    ∃ H cap chs, LibHeapAt H cap chs c ∧
      Barrier.Grow H (cap - tableCharge) tableCharge slot v ra sp (BitVec.ofNat 64 refTable) 0x40000#64 c := by
  obtain ⟨H, cap, chs, h⟩ := ok.freeListShape.libHeap
  have room := h.room
  rw [empty] at room
  simp only [reserved, ite_true] at room
  have capEq : cap - tableCharge + tableCharge = cap := by omega
  have tblNat : (BitVec.ofNat 64 refTable).toNat = refTable := by decide
  have readOnly : ∀ p ∈ VsaIris.MallocFast.roR, (vsaModel startupLive).reg c p.1 = p.2 := by
    intro p hp
    simp only [VsaIris.MallocFast.roR, List.mem_singleton] at hp
    subst hp
    show vsaReg c 3 = _
    unfold vsaReg
    rw [if_neg (by decide), gp]
    rfl
  have covered : ∀ (x : Nat × Nat), x ∈ f1Covered → x.1 ≤ (slot + BitVec.ofNat 64 0).toNat →
      (slot + BitVec.ofNat 64 0).toNat + 8 ≤ x.1 + x.2 →
      ∃ q n, (q, n) ∈ H ∧ heapStart ≤ q ∧ q + n ≤ heapEnd ∧ q ≤ (slot + BitVec.ofNat 64 0).toNat ∧
        (slot + BitVec.ofNat 64 0).toNat + 8 ≤ q + n := by
    intro x hx lo hi
    obtain ⟨⟨q, n⟩, he, elo, ehi⟩ := h.extents x hx
    obtain ⟨bl, bh⟩ := h.ready.block_bounds he
    exact ⟨q, n, he, bl, bh, by dsimp only at elo; omega, by dsimp only at ehi; omega⟩
  refine ⟨H, cap, chs, h, ?_⟩
  exact {
    ready := by rw [capEq]; exact RuntimeReady.of_heap h.ready leaf platform readOnly stack
    frame := frame
    table := by rw [tblNat]; exact h.tableIn
    tableAligned := by decide
    empty := by
      rw [tblNat]
      have e := empty
      simp only [Layout.off_ref_table_base, Nat.add_zero] at e
      exact BitVec.eq_of_toNat_eq e
    minorWsz := h.table.minorWsz
    charged := by unfold vsaChg; decide
    requestBig := by decide
    refCode := OCaml.Vm.Sim.caml_realloc_ref_table_loaded leaf.image
    genCode := OCaml.Vm.Sim.realloc_generic_table_loaded leaf.image
    slotLive := by
      rcases slotChunks with ⟨lo, hi⟩ | ⟨lo, hi⟩
      · exact covered (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) lo
          (by simp only [minorRegion] at *; omega)
      · exact covered (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) lo
          (by simp only [majorRegion] at *; omega)
    slotTable := by
      rw [tblNat]
      simp only [Realloc.tableBytes, refTable, WhileMinHeapChunks.refTablePayload]
      rcases slotChunks with ⟨lo, _⟩ | ⟨lo, _⟩ <;> simp only [minorRegion, majorRegion] at lo <;> omega
    slotWsz := by
      simp only [firstDomainPtr, heapStart, BitVec.toNat_ofNat]
      rcases slotChunks with ⟨lo, _⟩ | ⟨lo, _⟩ <;> simp only [minorRegion, majorRegion] at lo <;> omega }

/-- A byte inside a covered runtime region, outside the remembered-set struct,
is one the growth call keeps. -/
theorem kept_covered {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {sp : BitVec 64} {x : Nat × Nat} (cov : Covered H x) {a : Nat}
    (lo : x.1 ≤ a) (hi : a < x.1 + x.2) (struct : a < refTable ∨ refTable + 56 ≤ a) :
    Realloc.Kept H sp (BitVec.ofNat 64 refTable) a := by
  obtain ⟨⟨q, n⟩, he, elo, ehi⟩ := cov
  obtain ⟨bl, bh⟩ := h.ready.block_bounds he
  have tblNat : (BitVec.ofNat 64 refTable).toNat = refTable := by decide
  dsimp only at elo ehi
  refine Or.inr (Or.inr ⟨q, n, he, bl, bh, by omega, by omega, ?_⟩)
  rw [tblNat]; simp only [Realloc.tableBytes]; exact struct

/-- A static byte outside the allocator's globals is one the growth call keeps. -/
theorem kept_static {H : List (Nat × Nat)} {sp tbl : BitVec 64} {a : Nat} (low : a < heapStart)
    (notAlloc : ¬ allocGlobal a) : Realloc.Kept H sp tbl a :=
  Or.inr (Or.inl ⟨low, notAlloc⟩)

/-- A word whose bytes the growth call keeps (and that misses the slot) is unchanged. -/
theorem grow_word {H : List (Nat × Nat)} {capacity : Nat} {slot v ra sp tbl wsz : BitVec 64} {c c' : Config}
    (g : Barrier.GrowDone H capacity slot v ra sp tbl wsz c c') {x : Nat}
    (k : ∀ j, j < 8 → Realloc.Kept H sp tbl (x + j))
    (apart : x + 8 ≤ (slot + BitVec.ofNat 64 0).toNat ∨ (slot + BitVec.ofNat 64 0).toNat + 8 ≤ x) :
    bytesT c'.σ.mem x 8 = bytesT c.σ.mem x 8 := by
  apply Reloc.bytesT_congr
  intro j hj
  simp only [bytesT, g.kept _ (k j hj) (by omega)]

/-- Every footprint byte is one the growth call keeps. -/
theorem footprint_kept {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config} {sp : BitVec 64}
    (h : LibHeapAt H cap chs c) :
    ∀ v ∈ f1Footprint, ∀ a, v.lo ≤ a → a < v.hi → Realloc.Kept H sp (BitVec.ofNat 64 refTable) a := by
  have domCov := h.extents (WhileMinRuntime.domain, Layout.domainStateBytes) List.mem_cons_self
  have majCov := h.extents (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide)
  intro w hw a lo hi
  have domByte : 0x8007d150 ≤ a → a < 0x8007d150 + 928 → Realloc.Kept H sp (BitVec.ofNat 64 refTable) a :=
    fun l u => kept_covered h domCov l u (Or.inl (by
      simp only [refTable, WhileMinHeapChunks.refTablePayload]; omega))
  have freeByte : 0x80283000 ≤ a → a < 0x8037b000 → Realloc.Kept H sp (BitVec.ofNat 64 refTable) a :=
    fun l u => kept_covered h majCov l (by dsimp only; simp only [majorRegion]; omega) (Or.inr (by
      simp only [refTable, WhileMinHeapChunks.refTablePayload]; omega))
  rcases List.mem_cons.1 hw with rfl | hw
  · simp only [youngWord, f1Domain, WhileMinRuntime.domain, Layout.off_young_ptr] at lo hi
    exact domByte (by omega) (by omega)
  rcases List.mem_append.1 hw with hs | hd
  · have below := staticKept_below w hs
    refine kept_static (by simp only [Layout.sym_bss_end, heapStart] at *; omega) fun ga => ?_
    obtain ⟨i, hi', ilo, ihi⟩ := allocGlobal_ignored ga
    rcases staticKept_apart w hs i hi' with o | o <;> omega
  · simp only [dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.off_young_ptr,
        Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
        Layout.off_backtrace_active] at lo hi
    · exact domByte (by omega) (by omega)
    · exact domByte (by omega) (by omega)
    · exact domByte (by omega) (by omega)
    · exact domByte (by omega) (by omega)
    · exact domByte (by omega) (by omega)
    · exact freeByte (by omega) (by omega)

/-- No footprint byte is the slot: the slot lies in a heap chunk, outside the
private free block. -/
theorem footprint_notSlot {s : Nat} (slotChunks : InHeapChunks s 8)
    (slotPrivate : s + 8 ≤ privateRegion.lo ∨ privateRegion.hi ≤ s) :
    ∀ v ∈ f1Footprint, ∀ a, v.lo ≤ a → a < v.hi → a < s ∨ s + 8 ≤ a := by
  have sc : 0x80082000 ≤ s := by
    rcases slotChunks with ⟨lo, _⟩ | ⟨lo, _⟩ <;> simp only [minorRegion, majorRegion] at lo <;> omega
  simp only [privateRegion] at slotPrivate
  intro w hw a lo hi
  rcases List.mem_cons.1 hw with rfl | hw
  · left; simp only [youngWord, f1Domain, WhileMinRuntime.domain, Layout.off_young_ptr] at hi; omega
  rcases List.mem_append.1 hw with hs | hd
  · left; have := staticKept_below w hs; simp only [Layout.sym_bss_end] at this; omega
  · simp only [dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [f1Domain, WhileMinRuntime.domain, WhileMinRuntime.freeBlock, Layout.off_young_ptr,
        Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier,
        Layout.off_backtrace_active] at lo hi <;> omega

theorem toNat_of_add {x p K : BitVec 64} {k : Nat} (e : x = p + K) (hk : K.toNat = k)
    (small : p.toNat + k < 2 ^ 64) : x.toNat = p.toNat + k := by
  rw [e, BitVec.toNat_add, hk]
  omega

/-- **After the remembered set's growth, `f1Runtime` holds**: the footprint
the runtime invariant reads is kept by the call (static words, the
`Caml_state` record, the private free block), and newlib's heap gains the
storage block (`LibHeapAt.grow`). -/
theorem f1_afterGrow {c c' : Config} {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {slot v ra sp : BitVec 64}
    (ok : f1Runtime c) (h : LibHeapAt H cap chs c)
    (empty : (word c (refTable + Layout.off_ref_table_base)).toNat = 0)
    (g : Barrier.GrowDone H (cap - tableCharge) slot v ra sp (BitVec.ofNat 64 refTable) 0x40000#64 c c')
    (slotChunks : InHeapChunks (slot + BitVec.ofNat 64 0).toNat 8)
    (slotPrivate : (slot + BitVec.ofNat 64 0).toNat + 8 ≤ privateRegion.lo ∨
      privateRegion.hi ≤ (slot + BitVec.ofNat 64 0).toNat) :
    f1Runtime c' := by
  have room := h.room
  rw [empty] at room
  simp only [reserved, ite_true] at room
  have tblNat : (BitVec.ofNat 64 refTable).toNat = refTable := by decide
  have sc : minorRegion.lo ≤ (slot + BitVec.ofNat 64 0).toNat := by
    rcases slotChunks with ⟨lo, _⟩ | ⟨lo, _⟩ <;> simp only [minorRegion, majorRegion] at * <;> omega
  have domCov := h.extents (WhileMinRuntime.domain, Layout.domainStateBytes) List.mem_cons_self
  have majCov := h.extents (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide)
  /- every footprint byte is kept -/
  have keepByte : ∀ v ∈ f1Footprint, ∀ a, v.lo ≤ a → a < v.hi → (c'.σ.mem[a]?).getD 0 = (c.σ.mem[a]?).getD 0 :=
    fun w hw a lo hi => g.kept a (footprint_kept h w hw a lo hi) (footprint_notSlot slotChunks slotPrivate w hw a lo hi)
  have keep : ∀ x n, InFootprint x n → bytesT c'.σ.mem x n = bytesT c.σ.mem x n := by
    intro x n ⟨w, hw, lo, hi⟩
    apply Reloc.bytesT_congr
    intro j hj
    simp only [bytesT, keepByte w hw (x + j) (by omega) (by omega)]
  /- the heap invariant gains the storage block -/
  have domWord : ∀ off, off + 8 ≤ Layout.domainStateBytes →
      word c' (WhileMinRuntime.domain + off) = word c (WhileMinRuntime.domain + off) := fun off hoff =>
    grow_word g (fun j hj => kept_covered h domCov (by omega) (by omega)
      (Or.inl (by simp only [WhileMinRuntime.domain, refTable, WhileMinHeapChunks.refTablePayload,
        Layout.domainStateBytes] at *; omega)))
      (Or.inl (by simp only [WhileMinRuntime.domain, Layout.domainStateBytes, minorRegion] at *; omega))
  have fits := g.fresh
  have pr : (Realloc.request 0x40000#64).toNat = 264192 := by decide
  rw [pr] at fits
  have head : bytesT c'.σ.mem Layout.sym_caml_all_opened_channels 8 =
      bytesT c.σ.mem Layout.sym_caml_all_opened_channels 8 :=
    grow_word g (fun j hj => kept_static (by simp only [Layout.sym_caml_all_opened_channels, heapStart]; omega)
      (by unfold allocGlobal InRange; simp only [Layout.sym_caml_all_opened_channels]; omega))
      (Or.inl (by simp only [Layout.sym_caml_all_opened_channels, minorRegion] at *; omega))
  have links : ∀ b ∈ chs, bytesT c'.σ.mem (b + chanOffNext) 8 = bytesT c.σ.mem (b + chanOffNext) 8 := by
    intro b hb
    have st := h.recordsApart b hb (refTable, 56) (by decide)
    have mi := h.recordsApart b hb (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide)
    have ma := h.recordsApart b hb (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide)
    have n48 : chanOffNext + 8 ≤ chanRecordBytes := by decide
    dsimp only at st mi ma
    refine grow_word g (fun j hj => kept_covered h (h.records b hb) (by dsimp only; omega)
      (by dsimp only; omega) (by rcases st with o | o <;> omega)) ?_
    rcases slotChunks with ⟨lo, hi⟩ | ⟨lo, hi⟩ <;> simp only [minorRegion, majorRegion] at * <;> omega
  have pNat := g.nonzero
  have pAl := g.aligned
  refine f1_transfer keep (fun _ => ⟨_, _, chs, LibHeapAt.grow h g.ready.heap (charge := tableCharge)
    (by omega) (Nat.le_refl _) empty g.disjoint pNat (by omega) (lim := 262144) (by decide) (by decide)
    (by decide) ?_ ?_ ?_ ?_ (domWord _ (by decide)) (domWord _ (by decide)) head links⟩) ok
  · have b := g.base
    rw [tblNat] at b
    simp only [Layout.off_ref_table_base, Nat.add_zero]
    show (bytesT c'.σ.mem refTable 8).toNat = _
    rw [b]
  · show (bytesT c'.σ.mem (refTable + 8) 8).toNat = _
    have e := g.endField
    rw [tblNat] at e
    rw [toNat_of_add e (k := 264192) (by decide) (by simp only [heapEnd] at fits; omega), pr]
  · show (bytesT c'.σ.mem (refTable + 24) 8).toNat = _
    have q := g.ptr
    rw [show ((BitVec.ofNat 64 refTable) + BitVec.ofNat 64 24).toNat = refTable + 24 by decide] at q
    exact toNat_of_add q (by decide) (by simp only [heapEnd] at fits; omega)
  · show (bytesT c'.σ.mem (refTable + 32) 8).toNat = _
    have l := g.limit
    rw [tblNat] at l
    exact toNat_of_add l (by decide) (by simp only [heapEnd] at fits; omega)
end OCaml.Vm.Gc
