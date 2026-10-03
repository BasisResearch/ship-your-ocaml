import OCaml.Vm.Gc.PopFirstFootprint
import OCaml.Vm.Gc.ForwardedSetup

namespace OCaml.Vm.Gc.WorkQueue
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- Restored native values at the end of the forwarded first-field call. -/
def afterFirst (R : Nat → BitVec 64) (q : PendingCopy) (c : Config) :=
  FirstCall.linked (FirstField.args (firstRegs R q c))

theorem PopFirstPost.setup_carried {R q qs pl before after}
    (post : PopFirstPost R q qs pl before after) :
    GHolds after.σ (ForwardedField.setupCarried (afterFirst R q before)) := by
  apply gholds_select post.registers
  intro n v member
  simp only [ForwardedField.setupCarried, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h <;> cases h <;> rfl

theorem PopFirstPost.setup_input {R domain q qs pl count before after}
    (post : PopFirstPost R q qs pl before after) (ready : FirstReady R domain q before)
    (geometry : FieldCopy.Geometry q.source.toNat q.target.toNat count)
    (large : 1 < count) (one : R 24 = 1#64)
    (header : (word before (q.target.toNat - 8)).toNat / 1024 = count)
    (outside : OutWRange (firstFootprint R q) (q.target.toNat - 8) 8) :
    FieldCopy.SetupInput q.source.toNat q.target.toNat count after := by
  refine ⟨post.good, post.minstret, post.tick, post.code, ?_, geometry, large, ?_⟩
  · have pins : GHolds after.σ [(19,q.target),(18,q.source),(24,R 24)] :=
      ⟨gholds_lookup _ post.registers rfl, gholds_lookup _ post.registers rfl,
        gholds_lookup _ post.registers rfl, True.intro⟩
    simpa [FieldCopy.setupRegs, one] using pins
  · rw [frame_word (post.memory_frame ready) outside]
    exact header

/-- The composed prefix's framed source suffix and relocated first slot
supply the grey boundary, without per-store disjointness assumptions. -/
theorem PopFirstPost.grey_frame {R domain q qs pl before after μ fields}
    (post : PopFirstPost R q qs pl before after) (ready : FirstReady R domain q before)
    (geometry : FieldCopy.Geometry q.source.toNat q.target.toNat fields.length)
    (grey : (pendingPayload q fields).P pl q.target.toNat before)
    (forwarding : ∀ v, fields[0]? = some v →
      word before (word before q.target.toNat).toNat = relocWord μ pl v (word before q.target.toNat))
    (outside : ∀ i, 1 ≤ i → i < fields.length →
      OutWRange (firstFootprint R q) (scanPtr q.source.toNat i).toNat 8) :
    FieldCopy.RelocatingGrey q.source.toNat q.target.toNat fields pl μ after := by
  apply FieldCopy.relocating_grey_of_pending grey
  · intro v member
    exact post.first.trans (forwarding v member)
  · intro i lower bound
    have same := frame_word (post.memory_frame ready) (outside i lower bound)
    simpa only [geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)] using same

end OCaml.Vm.Gc.WorkQueue
