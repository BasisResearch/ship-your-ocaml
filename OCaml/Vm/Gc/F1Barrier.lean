import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Gc.BarrierRun
import OCaml.Refinement

/-!
# The write barrier's runtime facts under F1

What a2-sem's `BarrierRuntime f1Layout` needs from the F1 runtime invariant:
* `windowSeparated_of`: a window apart from the payload's runtime blocks
  (`f1Uses`) and from the open channel records is separated from the
  represented payload, at any loop geometry;
* `f1_table`: the remembered set in `Barrier.Table`'s form at every F1 state,
  from `LibHeapAt.table`.
-/

namespace OCaml.Vm.Gc
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives Boot

/-- The runtime blocks the represented payload observes: `f1Covered` without
the remembered-set struct. -/
def f1Uses : List (Nat × Nat) :=
  [(WhileMinRuntime.domain, Layout.domainStateBytes),
   (minorRegion.lo, minorRegion.hi - minorRegion.lo), (majorRegion.lo, majorRegion.hi - majorRegion.lo),
   (WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes),
   (WhileMinHeapChunks.codeBufferPayload, f1CodeBytes), (WhileMinHeapChunks.primTablePayload, 8 * f1PrimCapacity)]

theorem uses_covered : ∀ y ∈ f1Uses, y ∈ f1Covered := by decide

theorem lt_size_of_getElem? {α : Type} {a : Array α} {i : Nat} {v : α} (h : a[i]? = some v) : i < a.size := by
  rcases Nat.lt_or_ge i a.size with l | g
  · exact l
  · rw [Array.getElem?_eq_none g] at h
    cases h

/-- **A window apart from the payload's runtime blocks and the open records
is separated from the represented payload.** -/
theorem windowSeparated_of {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {high : Nat}
    (g : OCaml.LoopGeometry f1Layout P s c pl cp high) (ok : f1Runtime c)
    (code : (word c Layout.sym_caml_start_code).toNat = pl.codeBase)
    (stack : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high)
    {w : W} (bss : Layout.sym_bss_end ≤ w.lo)
    (uses : ∀ y ∈ f1Uses, w.hi ≤ y.1 ∨ y.1 + y.2 ≤ w.lo)
    (records : ∀ chs, OpenChannelList c.σ.mem chs → ∀ a ∈ chs, w.hi ≤ a ∨ a + chanRecordBytes ≤ w.lo)
    (named : ∀ x, NamedPlFoot pl s.world.named x → OutWRange [w] x 1) :
    WindowSeparated w P s c pl cp high := by
  have out : ∀ x n (y : Nat × Nat), y ∈ f1Uses → y.1 ≤ x → x + n ≤ y.1 + y.2 → OutWRange [w] x n :=
    fun x n y hy lo hi => ⟨by rcases uses y hy with h | h <;> omega, trivial⟩
  have dom := f1_domain ok
  have highEq : high = f1High := by rw [← stack, f1_stackHigh ok]
  have codeBase : pl.codeBase = WhileMinHeapChunks.codeBufferPayload := by
    rw [← code, ok.freeListShape.codeWord]; simp [WhileMinHeapChunks.codeBufferPayload]
  have prims : (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat =
      WhileMinHeapChunks.primTablePayload := by
    rw [ok.freeListShape.primsWord]; simp [WhileMinHeapChunks.primTablePayload]
  have codeFits := g.nursery.codeFits
  have primsFit := g.nursery.primsFit
  obtain ⟨chs, list, placed, -⟩ := g.nursery.channelsListed_mem
  exact {
    statics := bss
    named := named
    domain := by
      rw [dom]
      exact out _ _ (WhileMinRuntime.domain, Layout.domainStateBytes) List.mem_cons_self (Nat.le_refl _)
        (Nat.le_refl _)
    stack := by
      rw [highEq]
      exact out _ _ (WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) (by decide) (Nat.le_refl _)
        (Nat.le_refl _)
    code := fun i v hv => by
      have hi := lt_size_of_getElem? hv
      rw [codeBase]
      exact out _ _ (WhileMinHeapChunks.codeBufferPayload, f1CodeBytes) (by decide) (Nat.le_add_right _ _)
        (by dsimp only; omega)
    heap := fun l a o hp ho => by
      rcases g.nursery.heapChunks l a o hp ho with ⟨lo, hi⟩ | ⟨lo, hi⟩
      · exact out _ _ (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) lo
          (by simp only [minorRegion] at *; omega)
      · exact out _ _ (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) lo
          (by simp only [majorRegion] at *; omega)
    channels := fun id ch a hc hp => by
      have := records chs list a (placed id ch a hc hp)
      exact ⟨by unfold chanRecordBytes at this; omega, trivial⟩
    primitives := fun i name hn => by
      have hi := lt_size_of_getElem? hn
      rw [prims]
      exact out _ _ (WhileMinHeapChunks.primTablePayload, 8 * f1PrimCapacity) (by decide) (Nat.le_add_right _ _)
        (by dsimp only; omega) }

/-- With room, the table has its storage. -/
theorem LibHeapAt.storage {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c)
    (room : (word c (refTable + Layout.off_ref_table_ptr)).toNat < (word c (refTable + Layout.off_ref_table_limit)).toNat) :
    RefStorage H chs (word c (refTable + Layout.off_ref_table_base)).toNat
      (word c (refTable + Layout.off_ref_table_end)).toNat (word c (refTable + Layout.off_ref_table_ptr)).toNat
      (word c (refTable + Layout.off_ref_table_limit)).toNat := by
  rcases h.table.shape with ⟨_, p, l⟩ | st
  · rw [p, l] at room; exact absurd room (Nat.lt_irrefl 0)
  · exact st

/-- The storage lies in the allocator arena. -/
theorem RefStorage.bounds {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config} {b e p l : Nat}
    (h : LibHeapAt H cap chs c) (st : RefStorage H chs b e p l) :
    Vsa.Sim.DlHeap.heapStart ≤ b ∧ e ≤ Vsa.Sim.DlHeap.heapEnd := by
  obtain ⟨x, hx, lo, hi⟩ := st.covered
  have := h.ready.block_bounds hx
  dsimp only at lo hi
  have := st.limitEnd; have := st.low; have := st.ptrLimit
  omega

/-- **The remembered set in `Table`'s form at every F1 state.** -/
theorem f1_table {c : Config} (ok : f1Runtime c) :
    Barrier.Table (word c Layout.sym_Caml_state) (BitVec.ofNat 64 refTable)
      (word c (refTable + Layout.off_ref_table_ptr)) (word c (refTable + Layout.off_ref_table_limit)) c.σ.mem := by
  obtain ⟨H, cap, chs, h⟩ := ok.freeListShape.libHeap
  have dom := ok.freeListShape.domain
  have e104 : (BitVec.ofNat 64 f1Domain + BitVec.ofNat 64 104).toNat =
      WhileMinRuntime.domain + Layout.off_ref_table := by decide
  have e24 : (BitVec.ofNat 64 refTable + BitVec.ofNat 64 24).toNat = refTable + Layout.off_ref_table_ptr := by
    decide
  have e32 : (BitVec.ofNat 64 refTable + BitVec.ofNat 64 32).toNat = refTable + Layout.off_ref_table_limit := by
    decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dom, e104]; exact h.table.pointer
  · rw [e24]; rfl
  · rw [e32]; rfl
  · rw [dom]; exact ⟨by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide⟩
  · intro room
    have st := h.storage room
    obtain ⟨lo, hi⟩ := st.bounds h
    have := st.ptrAligned; have := st.ptrLimit; have := st.limitEnd; have := st.limitAligned; have := st.low
    have z : (word c (refTable + Layout.off_ref_table_ptr) + BitVec.ofNat 64 0).toNat =
        (word c (refTable + Layout.off_ref_table_ptr)).toNat := by simp
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [z] <;>
      simp only [Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd, Layout.sym_tohost] at * <;> omega

/-- Remembered-table identity is fixed by the actual domain/table words. -/
theorem f1_table_eq {c : Config} {tbl ptr limit : BitVec 64} (ok : f1Runtime c)
    (table : Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem) :
    tbl = BitVec.ofNat 64 refTable ∧ ptr = word c (refTable + Layout.off_ref_table_ptr) ∧
      limit = word c (refTable + Layout.off_ref_table_limit) := by
  have actual := f1_table ok
  have t : tbl = BitVec.ofNat 64 refTable := table.tableWord.symm.trans actual.tableWord
  subst tbl
  exact ⟨rfl, table.ptrWord.symm.trans actual.ptrWord, table.limitWord.symm.trans actual.limitWord⟩

/-- The open-channel list a geometry sees is the heap invariant's. -/
theorem LibHeapAt.records_of {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c : Config}
    (h : LibHeapAt H cap chs c) {chs' : List Nat} (list : OpenChannelList c.σ.mem chs') : chs' = chs :=
  OpenChannels.unique list h.channels

/-- **`BarrierRuntime.table` for F1**: the remembered set's words, their
arena bounds, and the struct and next entry separated from the payload. -/
theorem f1_tableRuntime {c : Config} (ok : f1Runtime c) :
    ∃ tbl ptr limit : BitVec 64, Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem ∧
      (tbl.toNat + 40 ≤ Vsa.Sim.DlHeap.heapEnd ∧
        (ptr.toNat < limit.toNat → ptr.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd)) ∧
      ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (high : Nat), OCaml.LoopGeometry f1Layout P s c pl cp high →
        (word c Layout.sym_caml_start_code).toNat = pl.codeBase →
        (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high →
        (∃ chains, NamedRepr c pl s.world.named chains) →
        WindowSeparated ⟨tbl.toNat, tbl.toNat + 40⟩ P s c pl cp high ∧
        (ptr.toNat < limit.toNat → WindowSeparated ⟨ptr.toNat, ptr.toNat + 8⟩ P s c pl cp high) := by
  obtain ⟨H, cap, chs, h⟩ := ok.freeListShape.libHeap
  have tblNat : (BitVec.ofNat 64 refTable).toNat = refTable := by decide
  refine ⟨_, _, _, f1_table ok, ⟨by rw [tblNat]; decide, fun room => ?_⟩, ?_⟩
  · have st := h.storage room
    obtain ⟨-, hi⟩ := st.bounds h
    have := st.ptrAligned; have := st.ptrLimit; have := st.limitEnd; have := st.limitAligned
    omega
  intro P s pl cp high g code stack names
  obtain ⟨chains, table⟩ := names
  rw [tblNat]
  refine ⟨?_, fun room => ?_⟩
  · apply windowSeparated_of g ok code stack (by decide) (by decide)
    · intro chs' list a ha
      rw [h.records_of list] at ha
      have := h.recordsApart a ha (refTable, 56) (by decide)
      dsimp only at this ⊢
      omega
    · intro x f
      have apart := h.named_fixed ⟨pl, s.world.named, chains, table, f⟩ (by decide : (refTable, 56) ∈ f1Covered)
      unfold VsaIris.InExt at apart
      exact ⟨by dsimp only at *; omega, trivial⟩
  · have st := h.storage room
    obtain ⟨lo, -⟩ := st.bounds h
    have := st.ptrAligned; have := st.ptrLimit; have := st.limitEnd; have := st.limitAligned; have := st.low
    apply windowSeparated_of g ok code stack
    · simp only [Vsa.Sim.DlHeap.heapStart, Layout.sym_bss_end] at *; omega
    · intro y hy
      rcases st.apartBlocks y (uses_covered y hy) with r | r <;> dsimp only <;> omega
    · intro chs' list a ha
      rw [h.records_of list] at ha
      rcases st.apartRecords a ha with r | r <;> dsimp only <;> omega
    · intro x f
      have apart := h.named_storage ⟨pl, s.world.named, chains, table, f⟩ st.nonzero
      unfold VsaIris.InExt at apart
      exact ⟨by dsimp only at *; omega, trivial⟩

/-- The insertion's two stores: the bumped `ptr` word and the entry. -/
def insertWindows (p : Nat) : List W :=
  [⟨refTable + Layout.off_ref_table_ptr, refTable + Layout.off_ref_table_ptr + 8⟩, ⟨p, p + 8⟩]

/-- Actual insertion windows miss every selected live channel record and
all static words. This uses RefStorage.apartRecords, rather than payload
placement chosen at an unrelated loop witness. -/
theorem LibHeapAt.insert_outside {H cap chs c} (h : LibHeapAt H cap chs c)
    (room : (word c (refTable + Layout.off_ref_table_ptr)).toNat <
      (word c (refTable + Layout.off_ref_table_limit)).toNat) :
    ∀ w ∈ insertWindows (word c (refTable + Layout.off_ref_table_ptr)).toNat,
      Layout.sym_bss_end ≤ w.lo ∧
      ∀ a ∈ chs, w.hi ≤ a ∨ a + chanRecordBytes ≤ w.lo := by
  have st := h.storage room
  obtain ⟨lo, hi⟩ := st.bounds h
  have low := st.low
  have lim := st.ptrLimit
  have ending := st.limitEnd
  have pa := st.ptrAligned
  have la := st.limitAligned
  intro w hw
  simp only [insertWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · refine ⟨by decide, ?_⟩
    intro a ha
    have apart := h.recordsApart a ha (refTable, 56) (by decide)
    dsimp only at apart ⊢
    have : Layout.off_ref_table_ptr + 8 ≤ 56 := by decide
    omega
  · refine ⟨?_, ?_⟩
    · have : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapStart := by decide
      dsimp only
      omega
    · intro a ha
      have apart := st.apartRecords a ha
      dsimp only
      omega

/-- The missing spatial supplier suffices at the precise insertion slot.
The struct store is excluded independently by CallerApart.covered. -/
theorem RefCustomApart.entry_outside {H cap chs c} (apart : RefCustomApart c)
    (h : LibHeapAt H cap chs c)
    (room : (word c (refTable + Layout.off_ref_table_ptr)).toNat <
      (word c (refTable + Layout.off_ref_table_limit)).toNat)
    {x : Nat} (inside : CustomFoot c x) :
    x < (word c (refTable + Layout.off_ref_table_ptr)).toNat ∨
      (word c (refTable + Layout.off_ref_table_ptr)).toNat + 8 ≤ x := by
  have st := h.storage room
  have lo := st.low
  have hi := st.limitEnd
  have lim := st.ptrLimit
  have pa := st.ptrAligned
  have la := st.limitAligned
  rcases apart with zero | separate
  · exact False.elim (st.nonzero zero)
  · have := separate x inside
    omega

/-- A byte outside both insertion windows is unchanged by the insertion log. -/
theorem insert_keep {m : Std.ExtHashMap Nat (BitVec 8)} {p : Nat} {v₁ v₂ : BitVec 64} {y : Nat}
    (out : ∀ w ∈ insertWindows p, y < w.lo ∨ w.hi ≤ y) :
    ((writeLog m [(refTable + Layout.off_ref_table_ptr, 8, v₁), (p, 8, v₂)])[y]?).getD 0 = (m[y]?).getD 0 := by
  have same : bytesT (writeLog m [(refTable + Layout.off_ref_table_ptr, 8, v₁), (p, 8, v₂)]) y 1 = bytesT m y 1 :=
    bytesT_writeLog_out _ (outLRange_of_forall fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · rcases out _ List.mem_cons_self with h | h <;> dsimp only at h ⊢ <;> omega
      · rcases out _ (List.mem_cons_of_mem _ List.mem_cons_self) with h | h <;> dsimp only at h ⊢ <;> omega)
  simpa using byte_of_bytesT same (i := 0) (by decide)

/-- **An insertion with room keeps the F1 heap invariant**: both stores land
in live blocks (the struct's and the storage's), miss the open records' links,
and the bumped pointer stays within the storage. -/
theorem LibHeapAt.insert {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat} {c c' : Config}
    (h : LibHeapAt H cap chs c) (slot : BitVec 64)
    (room : (word c (refTable + Layout.off_ref_table_ptr)).toNat < (word c (refTable + Layout.off_ref_table_limit)).toNat)
    (memory : c'.σ.mem = writeLog c.σ.mem [(refTable + Layout.off_ref_table_ptr, 8,
      word c (refTable + Layout.off_ref_table_ptr) + 8#64), ((word c (refTable + Layout.off_ref_table_ptr)).toNat, 8, slot)]) :
    LibHeapAt H cap chs c' := by
  have st := h.storage room
  obtain ⟨lo, hi⟩ := st.bounds h
  have := st.ptrAligned; have := st.ptrLimit; have := st.limitEnd; have := st.limitAligned; have := st.low
  have tableBlock := h.recordsApart
  obtain ⟨e, he, elo, ehi⟩ := h.extents (refTable, 56) (by decide)
  have tb := st.apartBlocks (refTable, 56) (by decide)
  have db := st.apartBlocks (WhileMinRuntime.domain, Layout.domainStateBytes) List.mem_cons_self
  dsimp only at elo ehi tb db
  /- every byte outside the two windows is unchanged -/
  have keep : ∀ y, (∀ w ∈ insertWindows (word c (refTable + Layout.off_ref_table_ptr)).toNat, y < w.lo ∨ w.hi ≤ y) →
      (c'.σ.mem[y]?).getD 0 = (c.σ.mem[y]?).getD 0 := fun y out => by rw [memory]; exact insert_keep out
  have word_keep : ∀ x, (∀ j, j < 8 → ∀ w ∈ insertWindows (word c (refTable + Layout.off_ref_table_ptr)).toNat,
      x + j < w.lo ∨ w.hi ≤ x + j) → word c' x = word c x := fun x h => by
    apply Reloc.bytesT_congr
    intro j hj
    simp only [bytesT, keep _ (h j hj)]
  have win : ∀ w ∈ insertWindows (word c (refTable + Layout.off_ref_table_ptr)).toNat,
      w = ⟨refTable + Layout.off_ref_table_ptr, refTable + Layout.off_ref_table_ptr + 8⟩ ∨
      w = ⟨(word c (refTable + Layout.off_ref_table_ptr)).toNat, (word c (refTable + Layout.off_ref_table_ptr)).toNat + 8⟩ := by
    intro w hw
    simp only [insertWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
    exact hw
  /- words apart from both windows: the struct's other words, the domain's pointer word -/
  have tableWord : ∀ off, (off + 8 ≤ Layout.off_ref_table_ptr ∨ Layout.off_ref_table_ptr + 8 ≤ off) →
      off + 8 ≤ 56 → word c' (refTable + off) = word c (refTable + off) := fun off o f =>
    word_keep _ fun j hj w hw => by
      rcases win w hw with rfl | rfl <;> dsimp only <;> simp only [Layout.off_ref_table_ptr] at * <;> omega
  have ptrWord : word c' (refTable + Layout.off_ref_table_ptr) = word c (refTable + Layout.off_ref_table_ptr) + 8#64 := by
    change bytesT c'.σ.mem _ 8 = _
    rw [memory]
    exact word_writeLog_at _ _ 0 _ _ rfl (outLRange_of_forall fun e he => by
      simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false] at he
      subst he
      dsimp only
      simp only [Layout.off_ref_table_ptr] at *
      omega)
  have ptrNat : (word c (refTable + Layout.off_ref_table_ptr) + 8#64).toNat =
      (word c (refTable + Layout.off_ref_table_ptr)).toNat + 8 := by
    rw [BitVec.toNat_add]
    simp only [Vsa.Sim.DlHeap.heapEnd] at hi
    simp only [BitVec.toNat_ofNat]
    omega
  have namedKeep : ∀ x, NamedRead c x → byte c' x = byte c x := by
    intro x read
    have fixed := h.named_fixed read (by decide : (refTable, 56) ∈ f1Covered)
    have storage := h.named_storage read st.nonzero
    rw [byte_total, byte_total]
    apply keep x
    intro w hw
    rcases win w hw with rfl | rfl
    · by_cases l : x < refTable + Layout.off_ref_table_ptr
      · exact Or.inl l
      · exact Or.inr (by apply Classical.byContradiction; intro no; apply fixed; constructor <;>
          dsimp only at * <;> simp only [Layout.off_ref_table_ptr] at * <;> omega)
    · by_cases l : x < (word c (refTable + Layout.off_ref_table_ptr)).toNat
      · exact Or.inl l
      · exact Or.inr (by apply Classical.byContradiction; intro no; apply storage; constructor <;>
          dsimp only at * <;> omega)
  have namedLedger : NamedLedger H (namedBlocked chs c') c' := by
    have kept := h.named.frame (c' := c') namedKeep
    simpa only [namedBlocked, tableWord Layout.off_ref_table_base (by decide) (by decide),
      tableWord Layout.off_ref_table_end (by decide) (by decide)] using kept
  have keepCustom : ∀ a, VsaIris.InExt (customTable, Layout.custom_table_bytes) a → byte c' a = byte c a := fun a inside => by
      rw [byte_total, byte_total]
      apply keep a
      intro w hw
      rcases win w hw with rfl | rfl
      · have sep : refTable + Layout.off_ref_table_ptr + 8 ≤ customTable := by decide
        have := inside.1
        right
        dsimp only at *
        omega
      · have sep := st.apartCustom
        have low := inside.1
        have high := inside.2
        dsimp only at *
        omega
  refine {
    room := by rw [tableWord Layout.off_ref_table_base (by decide) (by decide)]; exact h.room
    channelsBound := h.channelsBound
    ready := HeapReady.keep_windows h.ready (fun w hw => ?_) keep
    extents := h.extents
    custom := h.custom.frame keepCustom
    customSpace := h.space_frame namedKeep keepCustom
      (tableWord _ (by decide) (by decide)) (tableWord _ (by decide) (by decide))
    customRecords := h.customRecords
    channels := ?_
    records := h.records
    recordsApart := h.recordsApart
    recordsDisjoint := h.recordsDisjoint
    recordsAligned := h.recordsAligned
    table := ⟨?_, ?_, Or.inr ?_⟩
    tableIn := h.tableIn
    named := namedLedger }
  · rcases win w hw with rfl | rfl
    · exact Or.inl ⟨e, he, by simp only [Layout.off_ref_table_ptr]; omega,
        by simp only [Layout.off_ref_table_ptr]; omega⟩
    · obtain ⟨x, hx, xlo, xhi⟩ := st.covered
      dsimp only at xlo xhi
      exact Or.inl ⟨x, hx, by dsimp only; omega, by dsimp only; omega⟩
  · unfold OpenChannelList
    have head := word_keep Layout.sym_caml_all_opened_channels fun j hj w hw => by
      rcases win w hw with rfl | rfl <;> dsimp only <;>
        simp only [Layout.sym_caml_all_opened_channels, refTable, WhileMinHeapChunks.refTablePayload,
          Layout.off_ref_table_ptr, Vsa.Sim.DlHeap.heapStart] at * <;> omega
    change bytesT c'.σ.mem _ 8 = bytesT c.σ.mem _ 8 at head
    rw [head]
    refine OpenChannels.congr h.channels fun a ha => word_keep _ fun j hj w hw => ?_
    have ra := h.recordsApart a ha (refTable, 56) (by decide)
    have rs := st.apartRecords a ha
    have n48 : chanOffNext + 8 ≤ chanRecordBytes := by decide
    dsimp only at ra
    have p24 : Layout.off_ref_table_ptr = 24 := rfl
    rcases win w hw with rfl | rfl
    · dsimp only; rw [p24]; rcases ra with r | r <;> omega
    · dsimp only; rcases rs with r | r <;> omega
  · rw [word_keep _ fun j hj w hw => by
      rcases win w hw with rfl | rfl <;> dsimp only <;>
        simp only [WhileMinRuntime.domain, Layout.off_ref_table, refTable, WhileMinHeapChunks.refTablePayload,
          Layout.domainStateBytes, Layout.off_ref_table_ptr] at * <;> omega]
    exact h.table.pointer
  · rw [word_keep _ fun j hj w hw => by
      rcases win w hw with rfl | rfl <;> dsimp only <;>
        simp only [WhileMinRuntime.domain, Layout.off_minor_heap_wsz, refTable, WhileMinHeapChunks.refTablePayload,
          Layout.domainStateBytes, Layout.off_ref_table_ptr] at * <;> omega]
    exact h.table.minorWsz
  · rw [tableWord Layout.off_ref_table_base (by decide) (by decide),
      tableWord Layout.off_ref_table_end (by decide) (by decide),
      tableWord Layout.off_ref_table_limit (by decide) (by decide), ptrWord, ptrNat]
    exact {
      nonzero := st.nonzero, aligned := st.aligned, limitAligned := st.limitAligned
      ptrAligned := by omega
      low := by omega
      ptrLimit := by omega
      limitEnd := st.limitEnd, sized := st.sized, covered := st.covered, apartBlocks := st.apartBlocks
      apartRecords := st.apartRecords, apartCustom := st.apartCustom }

/-- **`BarrierRuntime.insert` for F1**: an insertion into the remembered set
with room keeps `f1Runtime`. -/
theorem f1_insert (c : Config) (tbl ptr limit slot : BitVec 64) (ok : f1Runtime c)
    (t : Barrier.Table (word c Layout.sym_Caml_state) tbl ptr limit c.σ.mem) (room : ptr.toNat < limit.toNat) :
    AllocationRuntime f1Runtime c (Barrier.insertLog tbl ptr slot) := by
  intro after memory _
  obtain ⟨H, cap, chs, h⟩ := ok.freeListShape.libHeap
  have dom := ok.freeListShape.domain
  have e104 : (BitVec.ofNat 64 f1Domain + BitVec.ofNat 64 104).toNat =
      WhileMinRuntime.domain + Layout.off_ref_table := by decide
  have e24 : (BitVec.ofNat 64 refTable + BitVec.ofNat 64 24).toNat = refTable + Layout.off_ref_table_ptr := by
    decide
  have e32 : (BitVec.ofNat 64 refTable + BitVec.ofNat 64 32).toNat = refTable + Layout.off_ref_table_limit := by
    decide
  have tblEq : tbl = BitVec.ofNat 64 refTable := by
    have tw := t.tableWord
    rw [dom, e104] at tw
    rw [← tw]
    exact h.table.pointer
  subst tblEq
  have ptrEq : ptr = word c (refTable + Layout.off_ref_table_ptr) := by
    have pw := t.ptrWord; rw [e24] at pw; exact pw.symm
  have limEq : limit = word c (refTable + Layout.off_ref_table_limit) := by
    have lw := t.limitWord; rw [e32] at lw; exact lw.symm
  subst ptrEq limEq
  have logEq : Barrier.insertLog (BitVec.ofNat 64 refTable) (word c (refTable + Layout.off_ref_table_ptr)) slot =
      [(refTable + Layout.off_ref_table_ptr, 8, word c (refTable + Layout.off_ref_table_ptr) + 8#64),
       ((word c (refTable + Layout.off_ref_table_ptr)).toNat, 8, slot)] := by
    simp only [Barrier.insertLog, e24]
    simp
  rw [logEq] at memory
  have st := h.storage room
  obtain ⟨lo, -⟩ := st.bounds h
  have := st.ptrLimit; have := st.limitEnd; have := st.low; have := st.limitAligned; have := st.ptrAligned
  have db := st.apartBlocks (WhileMinRuntime.domain, Layout.domainStateBytes) List.mem_cons_self
  have mb := st.apartBlocks (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide)
  have eb := st.apartBlocks (exeNameAddr, 6) (by decide)
  dsimp only at db mb eb
  have structApart := arena_footprint_apart (w := ⟨refTable + Layout.off_ref_table_ptr,
    refTable + Layout.off_ref_table_ptr + 8⟩) (by decide) (by decide) (by decide) (by decide)
  have entryApart := arena_footprint_apart (w := ⟨(word c (refTable + Layout.off_ref_table_ptr)).toNat,
    (word c (refTable + Layout.off_ref_table_ptr)).toNat + 8⟩) (by dsimp only; omega) (by dsimp only; omega)
    (by simp only [majorRegion] at *; omega) (by dsimp only; omega)
  refine f1_transfer (fun x n inside => ?_) (fun _ => ⟨H, cap, chs, h.insert slot room memory⟩) ok
  obtain ⟨v, member, vlo, vhi⟩ := inside
  rw [memory]
  apply bytesT_writeLog_out _ (outLRange_of_forall fun e he => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rcases structApart v member with a | a <;> dsimp only at a ⊢ <;> omega
  · rcases entryApart v member with a | a <;> dsimp only at a ⊢ <;> omega

end OCaml.Vm.Gc
