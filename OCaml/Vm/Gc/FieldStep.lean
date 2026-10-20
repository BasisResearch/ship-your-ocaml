import OCaml.Vm.Gc.MopupSlot
import OCaml.Vm.Gc.CopyEffect
import OCaml.Vm.Gc.ForwardingDomain

/-! # One mopup field at the slot level

Every route of a later field (`caml_oldify_mopup`'s scan of fields `1..`)
ends the same way: the copy's field holds the field's value under the
published forwarding table, which has only grown, and the scan has advanced
(`FieldStepped`). The verbatim copies (immediate, outside the nursery) keep
the table; the young case is a `caml_oldify_one` call over any route
(`MopupCall.slot_advance`). -/
namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- **A field stepped** at the slot level. -/
structure FieldStepped (copies : List PendingCopy) (pl : Place) (slot delta target index : BitVec 64)
    (before after : Config) : Prop where
  table : ∃ copies', (∃ new, copies' = new ++ copies) ∧ (ForwardingTable.eqv copies').P pl 0 after ∧
    word after (delta + slot).toNat =
      BitVec.ofNat 64 (ForwardingTable.relocation copies' (word before slot.toNat).toNat)
  pc : PCAt (if advanceAgain target index after then pc else exitPc) after
  registers : GHolds after.σ (regs (slot + 8#64) delta target (index + 1#64))
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

/-- The copy path's loop choice reads the header after its store. -/
theorem again_after {slot delta target index before after}
    (memory : after.σ.mem = writeLog before.σ.mem (copyLog slot delta before)) :
    again slot delta target index before = advanceAgain target index after := by
  unfold again advanceAgain loads word
  rw [memory]
  simp only [List.tail_cons, List.headD_cons, read8_value]

/-- A verbatim copy: the value is no published source, so the table is the
identity on it and survives the store. -/
theorem CopyEffect.stepped {w copies pl slot delta target index before after}
    (post : CopyEffect w slot delta target index before after)
    (view : (ForwardingTable.eqv copies).P pl 0 before)
    (outside : ForwardingTable.Outside copies (copyLog slot delta before))
    (absent : ∀ q ∈ copies, q.source.toNat ≠ (word before slot.toNat).toNat) :
    FieldStepped copies pl slot delta target index before after := by
  refine ⟨⟨copies, ⟨[], rfl⟩, ForwardingTable.frame view post.memory outside, ?_⟩, ?_, post.registers,
    post.good, post.tick, post.minstret, post.code⟩
  · rw [post.destination, ForwardingTable.identity_of_absent absent]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← again_after post.memory]; exact post.pc

/-- The call path's register view of the field. -/
structure CallView (R : Nat → BitVec 64) (slot delta target index : BitVec 64) (before : Config) : Prop where
  r8 : R 8 = slot
  r18 : R 18 = delta
  r19 : R 19 = target
  r9 : R 9 = index
  r10 : R 10 = word before slot.toNat
  r11 : R 11 = delta + slot

/-- A young field: any route's call, then the advance. -/
theorem SlotAdvanced.stepped {R copies pl slot delta target index before after}
    (post : MopupCall.SlotAdvanced R copies pl before after) (view : CallView R slot delta target index before) :
    FieldStepped copies pl slot delta target index before after := by
  obtain ⟨e, copies', mid, -, done, memory, pcAt⟩ := post.call
  have viewMid := done.table
  have tableAfter : (ForwardingTable.eqv copies').P pl 0 after :=
    ForwardingTable.frame viewMid (log := []) (by rw [memory]; rfl) (fun _ _ => ⟨trivial, trivial⟩)
  have root := done.root
  have l11 : MopupCall.site.toSlot.linked R 11 = R 11 := rfl
  have l10 : MopupCall.site.toSlot.linked R 10 = R 10 := rfl
  rw [l11, l10] at root
  have again : advanceAgain (R 19) (R 9) mid = advanceAgain (R 19) (R 9) after := by
    unfold advanceAgain word; rw [memory]
  refine ⟨⟨copies', done.grows, tableAfter, ?_⟩, ?_, ?_, post.good, post.tick, post.minstret, post.code⟩
  · rw [← view.r11, ← view.r10]
    simpa only [word, memory] using root
  · rw [← view.r19, ← view.r9, ← again]; exact pcAt
  · rw [← view.r8, ← view.r18, ← view.r19, ← view.r9]; exact post.registers

end OCaml.Vm.Gc.FieldCopy
