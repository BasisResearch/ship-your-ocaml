import OCaml.Vm.Sim.BarrierKeep
import OCaml.Vm.Gc.F1Grow

/-!
# The represented payload across the remembered set's growth (F1)

`observed_kept`: every byte the represented barrier state reads
(`BarrierObserved`) is one the growth call keeps (`Realloc.Kept`): static
words outside newlib's allocator, the runtime's live blocks other than the
remembered-set struct (the `Caml_state` record, code, VM stack, heap chunks,
channel records, primitive table), and the invocation's native words above the
barrier's `sp`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives OCaml.Vm.Boot.Startup
  VsaIris.VsaHeap OCaml.Vm.Gc

theorem barrierStatics_kept : ∀ a ∈ barrierStatics, ∀ x, a ≤ x → x < a + 8 → x < heapStart ∧ ¬ allocGlobal x := by
  intro a ha x lo hi
  simp only [barrierStatics, List.mem_cons, List.not_mem_nil, or_false] at ha
  refine ⟨?_, fun g => ?_⟩
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
        Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_caml_all_opened_channels,
        Layout.sym_caml_prim_table, Layout.off_prim_contents, heapStart] at hi ⊢ <;> omega
  · unfold allocGlobal InRange at g
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Layout.sym_Caml_state, Layout.sym_caml_start_code, Layout.sym_caml_atom_table,
        Layout.sym_caml_global_data, Layout.sym_oo_last_id, Layout.sym_caml_all_opened_channels,
        Layout.sym_caml_prim_table, Layout.off_prim_contents] at lo hi <;> omega

/-- **Every byte the represented barrier state reads is kept by the growth call.** -/
theorem observed_kept {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high : Nat}
    {D : InvocationData} {H : List (Nat × Nat)} {cap : Nat} {chs : List Nat}
    (ok : f1Runtime c) (h : LibHeapAt H cap chs c) (g : OCaml.LoopGeometry f1Layout P s c pl cp high)
    (data : VmPayload P s c pl cp sp high) (low : high - Layout.stackBytes ≤ sp) (small : D.nativeSp < 2 ^ 64) :
    ∀ x, BarrierObserved P s c pl cp sp D x → Realloc.Kept H (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 refTable) x := by
  have region : ∀ y ∈ f1Covered, (y.1 + y.2 ≤ refTable ∨ refTable + 56 ≤ y.1 ∨ y = (refTable, 56)) := by decide
  /- a byte of a covered runtime block other than the struct -/
  have block : ∀ y ∈ f1Covered, y ≠ (refTable, 56) → ∀ x, y.1 ≤ x → x < y.1 + y.2 →
      Realloc.Kept H (BitVec.ofNat 64 D.nativeSp) (BitVec.ofNat 64 refTable) x := by
    intro y hy ne x lo hi
    refine kept_covered h (h.extents y hy) lo hi ?_
    rcases region y hy with r | r | r
    · left; omega
    · right; omega
    · exact absurd r ne
  have highEq : high = f1High := by rw [← data.stackHigh, f1_stackHigh ok]
  have codeBase : pl.codeBase = Boot.WhileMinHeapChunks.codeBufferPayload := by
    rw [← data.codeBase, ok.freeListShape.codeWord]; simp [Boot.WhileMinHeapChunks.codeBufferPayload]
  have prims : (word c (Layout.sym_caml_prim_table + Layout.off_prim_contents)).toNat =
      Boot.WhileMinHeapChunks.primTablePayload := by
    rw [ok.freeListShape.primsWord]; simp [Boot.WhileMinHeapChunks.primTablePayload]
  have codeFits := g.nursery.codeFits
  have primsFit := g.nursery.primsFit
  obtain ⟨len, -⟩ := data.stack
  intro x obs
  cases obs with
  | static ha span =>
    obtain ⟨l, u⟩ := barrierStatics_kept _ ha x span.1 span.2
    exact Gc.kept_static l u
  | domain span =>
    rw [f1_domain ok] at span
    exact block _ List.mem_cons_self (by decide) x span.1 span.2
  | code hc span =>
    have hi := lt_size_of_getElem? hc
    rw [codeBase] at span
    exact block (Boot.WhileMinHeapChunks.codeBufferPayload, f1CodeBytes) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [f1CodeBytes] at *; omega)
  | stack hs span =>
    have hi := (List.getElem?_eq_some_iff.1 hs).1
    rw [highEq] at low len
    exact block (f1High - Layout.stackBytes, Layout.stackBytes) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega)
      (by dsimp only; have := span.2; simp only [f1High, Boot.WhileMinEntry.high, Layout.stackBytes] at *; omega)
  | header ho hp span =>
    rcases g.nursery.heapChunks _ _ _ hp ho with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact block (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [minorRegion] at *; omega)
    · exact block (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [majorRegion] at *; omega)
  | fields ho hp span =>
    rcases g.nursery.heapChunks _ _ _ hp ho with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact block (minorRegion.lo, minorRegion.hi - minorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [minorRegion] at *; omega)
    · exact block (majorRegion.lo, majorRegion.hi - majorRegion.lo) (by decide) (by decide) x
        (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [majorRegion] at *; omega)
  | channel hc hp span =>
    obtain ⟨chs', list, placed, -⟩ := g.nursery.channelsListed
    have ha := placed _ _ _ hc hp
    rw [h.records_of list] at ha
    have st := h.recordsApart _ ha (refTable, 56) (by decide)
    dsimp only at st
    refine kept_covered h (h.records _ ha) span.1 (by dsimp only; have := span.2; unfold chanRecordBytes; omega) ?_
    have := span.1; have := span.2
    rcases st with o | o
    · left; unfold chanRecordBytes at o; omega
    · right; omega
  | prim hn span =>
    have hi := lt_size_of_getElem? hn
    rw [prims] at span
    exact block (Boot.WhileMinHeapChunks.primTablePayload, 8 * f1PrimCapacity) (by decide) (by decide) x
      (by dsimp only; have := span.1; omega) (by dsimp only; have := span.2; simp only [f1PrimCapacity] at *; omega)
  | native hr span =>
    left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    have := span.1
    omega

end OCaml.Vm.Sim
