import OCaml.Vm.Gc.SingleFieldQueuedChild
import OCaml.Vm.Gc.ForwardingComplete
import OCaml.Vm.Gc.TailProgress

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- Queue insertion exposes the same two forwarding words as a size-one
prefix; its additional intrusive link is orthogonal to the partial table. -/
theorem Fresh.ContextQueued.forwarding {source root sp target log qs pl writes before after}
    (post : Fresh.ContextQueued source root sp target log qs pl writes before after) :
    (forwardingEqv ⟨source,target⟩).P pl 0 after :=
  ⟨post.data.queue.first.forwardedHeader,post.data.queue.first.target⟩

/-- A parent prefix followed by allocation and child insertion publishes
both copies. Existing entries and the parent's forwarding words survive
through explicit finite footprints of the combined suffix. -/
theorem SingleField.QueuedChild.table {q root sp payload log qs pl copies before after}
    (post : SingleField.QueuedChild q root sp payload log qs pl before after)
    (view : (ForwardingTable.eqv copies).P pl 0 before)
    (window : WriteWindow q.source 8)
    (parentOutside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root))
    (suffixOutside : ForwardingTable.Outside (q :: copies)
      (log ++ Fresh.contextQueueEffect (SingleField.child q root before) payload q.target
        (Enqueue.prefixLog q.source q.target root ++ log) qs before)) :
    (ForwardingTable.eqv (⟨SingleField.child q root before,payload⟩ :: q :: copies)).P pl 0 after := by
  have memory : after.σ.mem = writeLog before.σ.mem
      (Enqueue.prefixLog q.source q.target root ++
        (log ++ Fresh.contextQueueEffect (SingleField.child q root before) payload q.target
          (Enqueue.prefixLog q.source q.target root ++ log) qs before)) := by
    simpa only [List.append_assoc] using post.memory
  have parent := ForwardingTable.publish_then view memory window parentOutside suffixOutside
  have child := post.forwarding
  intro p member
  rcases List.mem_cons.mp member with same | member
  · subst p; exact child
  · exact parent p member

namespace ForwardingTable

/-- A batch of actual publications preserves table completeness when every
source not in that batch retains its header. This permits both parent and
multi-field child to be forwarded by one terminal iteration. -/
theorem Complete.extend_many {sources copies before after} {added : List PendingCopy}
    (complete : Complete sources copies before)
    (preserved : ∀ source ∈ sources, (∀ q ∈ added, source ≠ q.source) →
      word after (source - 8#64).toNat = word before (source - 8#64).toNat) :
    Complete sources (added ++ copies) after := by
  intro source member zero
  by_cases found : ∃ q ∈ added, q.source = source
  · obtain ⟨q,hq,equal⟩ := found
    exact ⟨q,List.mem_append_left _ hq,equal⟩
  · have outside : ∀ q ∈ added, source ≠ q.source := by
      intro q hq same
      exact found ⟨q,hq,same.symm⟩
    obtain ⟨q,hq,equal⟩ := complete source member ((preserved source member outside).symm.trans zero)
    exact ⟨q,List.mem_append_right _ hq,equal⟩

/-- Strict copying progress from retained table coverage, even when one
iteration publishes several fresh objects. Zero headers never become live
again because every old entry survives in the final concrete table. -/
theorem Complete.progress {sources copies next pl before after source}
    (complete : Complete sources copies before)
    (view : (eqv next).P pl 0 after)
    (retained : ∀ q ∈ copies, q ∈ next)
    (member : source ∈ sources)
    (fresh : word before (source - 8#64).toNat ≠ 0)
    (forwarded : word after (source - 8#64).toNat = 0) :
    tailRemaining sources after < tailRemaining sources before := by
  apply countP_strict (a := source) member (by simpa using fresh) (by rw [forwarded]; decide)
  intro other otherMember nonzero
  have notZero : word before (other - 8#64).toNat ≠ 0 := by
    intro zero
    obtain ⟨q,hq,same⟩ := complete other otherMember zero
    have finalZero : word after (other - 8#64).toNat = 0 := same ▸ (view q (retained q hq)).1
    rw [finalZero] at nonzero
    contradiction
  simpa using notZero

end ForwardingTable

/-- The concrete two-publication exit covers all zero headers when the
remaining original source headers lie outside its exact store log. -/
theorem SingleField.QueuedChild.complete {q root sp payload log qs pl copies sources before after}
    (post : SingleField.QueuedChild q root sp payload log qs pl before after)
    (complete : ForwardingTable.Complete sources copies before)
    (outside : ∀ source ∈ sources, source ≠ q.source → source ≠ SingleField.child q root before →
      OutLRange ((Enqueue.prefixLog q.source q.target root ++ log) ++
        Fresh.contextQueueEffect (SingleField.child q root before) payload q.target
          (Enqueue.prefixLog q.source q.target root ++ log) qs before) (source - 8#64).toNat 8) :
    ForwardingTable.Complete sources (⟨SingleField.child q root before,payload⟩ :: q :: copies) after := by
  apply ForwardingTable.Complete.extend_many (added := [⟨SingleField.child q root before,payload⟩,q]) complete
  intro source member different
  have parent := different q (by simp)
  have child := different ⟨SingleField.child q root before,payload⟩ (by simp)
  simp only [word,post.memory,bytesT_writeLog_out _ (outside source member parent child)]

end OCaml.Vm.Gc
