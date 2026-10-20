import OCaml.Vm.Sim.OpenOutObserved
import OCaml.Vm.Sim.OpenGeometry

/-!
# The new record's separation (`NewChannelPlaced`)

The record `caml_open_descriptor_in` mallocs is fresh against newlib's live
blocks (`OpenedIn.fresh`), and every region the geometry places lies in a
covered block: the VM stack, the code buffer, the atom table, the primitive
table, `Caml_state`, the minor heap (objects, the custom block and the free
nursery), the major chunk (objects and the private region), and the open
records. `fresh_outW` turns freshness against a covered block into the
geometry's `OutWRange`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm.Primitives.Channel

/-- **A fresh record misses a covered range.** -/
theorem fresh_outW {H : List (Nat × Nat)} {p : Nat}
    (fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (p, recordBytes) y → ¬ VsaIris.InExt e y) {e : Nat × Nat}
    (cov : Gc.Covered H e) (pos : 0 < e.2) {lo hi : Nat} (sub1 : e.1 ≤ lo) (sub2 : hi ≤ e.1 + e.2) :
    OutWRange [⟨lo, hi⟩] p (chanOffBuff + ioBufferSize) := by
  have f := Gc.fresh_apart_covered fresh cov pos (n := recordBytes) (by unfold recordBytes; decide) (Nat.le_refl _)
  simp only [OutWRange, and_true]
  unfold recordBytes chanOffBuff ioBufferSize at *
  omega

/-- A range inside a covered region misses a fresh record (the other
direction of `fresh_outW`). -/
theorem fresh_outW_rev {H : List (Nat × Nat)} {p : Nat}
    (fresh : ∀ e ∈ H, ∀ y, VsaIris.InExt (p, recordBytes) y → ¬ VsaIris.InExt e y) {e : Nat × Nat}
    (cov : Gc.Covered H e) (pos : 0 < e.2) {a n : Nat} (sub1 : e.1 ≤ a) (sub2 : a + n ≤ e.1 + e.2) :
    OutWRange [⟨p, p + (chanOffBuff + ioBufferSize)⟩] a n := by
  have f := Gc.fresh_apart_covered fresh cov pos (n := recordBytes) (by unfold recordBytes; decide) (Nat.le_refl _)
  simp only [OutWRange, and_true]
  unfold recordBytes chanOffBuff ioBufferSize at *
  omega

/-- **The new record's separation** at a config `c'` whose `Caml_state` and
primitive-table words are the entry's and whose free nursery lies in the minor
heap, for a state `t` whose heap is the entry's plus one fresh object in the
minor heap (the custom block). -/
theorem open_out_placed {L : OCaml.Layout} {P : Prog} {s t : St} {pl : Place} {cp : ChanPlace} {spV high : Nat}
    {live : Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop} {k : Nat}
    {H : List (Nat × Nat)} {cap cap' charge : Nat} {sp ra r0 r1 r2 v head : BitVec 64} {c c' d : Config}
    {ob : Obj} {block : Nat}
    (o : OpenedOut live Ready state k H cap' charge sp ra r0 r1 r2 v head c d)
    (heap : Gc.LibHeapAt H cap (Gc.placedChannels cp s.world.chans.length) c)
    (h : OutInput live H cap' charge sp ra r0 r1 r2 v head c)
    (pins : Gc.F1Pins c) (data : VmPayload P s c pl cp spV high) (g : OCaml.LoopGeometry L P s c pl cp high)
    (heapT : t.heap = (s.heap.alloc ob).1) (worldT : t.world = s.world)
    (placedT : pl.φ (s.heap.alloc ob).2 = some block)
    (blockLow : Gc.minorRegion.lo + 8 ≤ block) (blockHigh : block + 8 * ob.wosize ≤ Gc.minorRegion.hi)
    (domain : word c' Layout.sym_Caml_state = word c Layout.sym_Caml_state)
    (prims : word c' (Layout.sym_caml_prim_table + Layout.off_prim_contents) =
      word c (Layout.sym_caml_prim_table + Layout.off_prim_contents))
    (limitLow : Gc.minorRegion.lo ≤ (runtimeFields c').youngLimit)
    (ptrHigh : (runtimeFields c').youngPtr ≤ Gc.minorRegion.hi) :
    NewChannelPlaced P t c' pl cp high o.opening.record.toNat := by
  have fresh := o.opening.fresh
  have cov : ∀ e ∈ Gc.f1Covered, Gc.Covered H e := heap.extents
  have pLow := o.opening.low
  have pHigh := o.opening.high
  have top := high_eq pins data h.domain
  have minorIn : (Gc.minorRegion.lo, Gc.minorRegion.hi - Gc.minorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
  have majorIn : (Gc.majorRegion.lo, Gc.majorRegion.hi - Gc.majorRegion.lo) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
  have mh : Gc.minorRegion.lo ≤ Gc.minorRegion.hi := by decide
  have Mh : Gc.majorRegion.lo ≤ Gc.majorRegion.hi := by decide
  refine {
    stack := ?_, heap := ?_, arena := ?_, low := ?_, code := ?_, atoms := ?_, prims := ?_, apart := ?_,
    domain := ?_, nursery := ?_, private_ := ?_ }
  · have he : (Boot.WhileMinEntry.high - Layout.stackBytes, Layout.stackBytes) ∈ Gc.f1Covered := by
      simp [Gc.f1Covered]
    have below : Layout.stackBytes ≤ Boot.WhileMinEntry.high := by decide
    simp only [stackWindow, top]
    exact fresh_outW fresh (cov _ he) (by decide) (Nat.le_refl _) (by dsimp only; omega)
  · intro l a ob' placed found
    rw [heapT] at found
    rcases heap_alloc_get found with old | ⟨rfl, rfl⟩
    · rcases g.nursery.heapChunks l a ob' placed old with ⟨cl, ch⟩ | ⟨cl, ch⟩
      · exact fresh_outW_rev fresh (cov _ minorIn) (by decide) (by dsimp only; omega) (by dsimp only; omega)
      · exact fresh_outW_rev fresh (cov _ majorIn) (by decide) (by dsimp only; omega) (by dsimp only; omega)
    · rw [placedT] at placed
      cases placed
      exact fresh_outW_rev fresh (cov _ minorIn) (by decide) (by dsimp only; omega) (by dsimp only; omega)
  · unfold recordBytes at pHigh; unfold chanOffBuff ioBufferSize; omega
  · have : Layout.sym_bss_end ≤ Vsa.Sim.DlHeap.heapStart := by decide
    omega
  · rw [codeBase_eq pins data]
    have fit := g.nursery.codeFits
    have he : (Boot.WhileMinHeapChunks.codeBufferPayload, Gc.f1CodeBytes) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
    exact fresh_outW fresh (cov _ he) (by decide) (Nat.le_refl _) (by dsimp only; omega)
  · rw [atomBase_eq pins data]
    have he : (Gc.atomTableAddr, 2056) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
    exact fresh_outW fresh (cov _ he) (by decide) (Nat.le_refl _) (Nat.le_of_eq (by unfold atomTableBytes; rfl))
  · intro i name hi
    rw [prims, pins.primsWord]
    have size : i < P.prims.size := (Array.getElem?_eq_some_iff.mp hi).1
    have fit := g.nursery.primsFit
    have he : (Boot.WhileMinHeapChunks.primTablePayload, 8 * Gc.f1PrimCapacity) ∈ Gc.f1Covered := by
      simp [Gc.f1Covered]
    have e : (BitVec.ofNat 64 Boot.WhileMinHeapChunks.primTablePayload).toNat =
        Boot.WhileMinHeapChunks.primTablePayload := rfl
    rw [e]
    exact fresh_outW fresh (cov _ he) (by decide) (by dsimp only; omega) (by dsimp only; omega)
  · intro id ch a hc hp
    rw [worldT] at hc
    have mem : a ∈ Gc.placedChannels cp s.world.chans.length :=
      Gc.mem_placedChannels.2 ⟨id, (List.getElem?_eq_some_iff.mp hc).1, hp⟩
    have f := Gc.fresh_apart_covered fresh (x := (a, Gc.chanRecordBytes)) (heap.records a mem)
      (by show 0 < Gc.chanRecordBytes; decide) (n := recordBytes)
      (by unfold recordBytes; decide) (Nat.le_refl _)
    dsimp only at f
    unfold recordBytes Gc.chanRecordBytes chanOffBuff ioBufferSize at *
    omega
  · rw [domain, h.domain]
    have he : (Boot.WhileMinRuntime.domain, Layout.domainStateBytes) ∈ Gc.f1Covered := by simp [Gc.f1Covered]
    exact fresh_outW fresh (cov _ he) (by decide) (Nat.le_refl _) (Nat.le_refl _)
  · simp only [Gc.nurseryFree]
    exact fresh_outW fresh (cov _ minorIn) (by decide) limitLow (by dsimp only; omega)
  · exact fresh_outW fresh (cov _ majorIn) (by decide) (by decide) (by decide)

end OCaml.Vm.Sim
