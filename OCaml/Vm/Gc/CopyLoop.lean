import OCaml.Vm.Gc.CopyChoice

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives

/-- Reachable-head coverage including fresh multi-field child exits. The
heap/free-list invariant must supply these concrete data choices. Other tags,
allocator alternatives, and full collector ownership remain open. -/
structure CopyCoverage (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config) : Prop where
  returnDifferent : OldifyReturn.returnWord sp initial ≠ SingleField.pc
  choices : ∀ copies q root c, Steps initial c → Head sp sources pl initial copies q root c →
    CopyChoice sp sources copies pl q root c

/-- The old ordinary coverage is a special case of the wider branch set. -/
theorem Coverage.toCopy {sp sources pl initial} (coverage : Coverage sp sources pl initial) :
    CopyCoverage sp sources pl initial :=
  ⟨coverage.returnDifferent,fun copies q root c reached head =>
    CopyChoice.ordinary (coverage.choices copies q root c reached head)⟩

/-- Fold single-field back edges and both scalar and queued-child exits,
retaining properties closed under the concrete publication batches. -/
theorem run_copy_loop_tracked {sp sources pl initial track}
    (coverage : CopyCoverage sp sources pl initial)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next) :
    Triple (TrackedAt sp sources pl initial track) (TrackedDone sp sources pl initial track) := by
  apply loop_to_exit (entry := SingleField.pc) (tailRemaining sources)
  · rintro c ⟨copies,q,root,head,_,_⟩
    exact head.pc
  · rintro c ⟨copies,finished,_⟩ pc
    exact coverage.returnDifferent (Option.some.inj (finished.pc.symm.trans pc))
  · rintro c ⟨copies,q,root,head,reached,tracked⟩
    obtain ⟨after,nextCopies,run,publication,post,less⟩ :=
      head.step_copy reached (coverage.choices copies q root c reached head)
    have next := extend copies q root c nextCopies head publication tracked
    refine ⟨after,run,?_,less⟩
    rcases post with ⟨child,root,head,reached⟩ | finished
    · exact Or.inl ⟨_,child,root,head,reached,next⟩
    · exact Or.inr ⟨_,finished,next⟩

/-- Whole copying loop from an allocated single-field entry. The final
complete forwarding table stays within the original finite young source set,
including the two-publication queued-child exit. -/
theorem run_copy_from_head {sp sources pl initial copies q root}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : CopyCoverage sp sources pl initial)
    (bounded : ForwardingTable.Bounded copies sources) :
    FnSummary SingleField.pc (fun c => c = initial)
      (TrackedDone sp sources pl initial (fun copies => ForwardingTable.Bounded copies sources)) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  apply run_copy_loop_tracked coverage ?_ initial ⟨copies,q,root,head,Steps.refl initial,bounded⟩
  intro copies q root c next head publication bounded
  exact publication.bounded bounded head.member

end OCaml.Vm.Gc.SingleTail
