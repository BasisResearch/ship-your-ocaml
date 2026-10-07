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

end OCaml.Vm.Gc
