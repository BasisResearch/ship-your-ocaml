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

/-- An operational head with a representation view indexed by the actual
published table. The index permits source objects to leave the unforwarded
view as the table grows. -/
structure IndexedHead (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : List PendingCopy → Config → Prop)
    (copies : List PendingCopy) (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop
    extends Head sp sources pl initial copies q root c where
  reached : Steps initial c
  tracked : track copies
  observation : observe copies c

structure IndexedAt (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : List PendingCopy → Config → Prop) (c : Config) : Prop where
  state : ∃ copies q root, IndexedHead sp sources pl initial track observe copies q root c

structure IndexedReturn (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : List PendingCopy → Config → Prop)
    (copies : List PendingCopy) (c : Config) : Prop extends Finished sp sources pl initial copies c where
  tracked : track copies
  observation : observe copies c

structure IndexedDone (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : List PendingCopy → Config → Prop) (c : Config) : Prop where
  state : ∃ copies, IndexedReturn sp sources pl initial track observe copies c

/-- Shared copying fold for views indexed by the growing table. Its frame
law consumes the exact stores and publication batch, rather than any assumed
execution. Clients derive this law from concrete ownership and Eqv transport. -/
theorem run_copy_loop_indexed {sp sources pl initial track observe}
    (coverage : CopyCoverage sp sources pl initial)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next)
    (frame : ∀ copies q root before after next log, Head sp sources pl initial copies q root before → track copies →
      Publication sources copies q (SingleField.child q root before) next → CopyEffect q root sp before log →
      after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log) →
      observe copies before → observe next after) :
    Triple (IndexedAt sp sources pl initial track observe) (IndexedDone sp sources pl initial track observe) := by
  apply loop_to_exit (entry := SingleField.pc) (tailRemaining sources)
  · intro c pre
    obtain ⟨copies,q,root,head⟩ := pre.state
    exact head.pc
  · intro c post pc
    obtain ⟨copies,finished⟩ := post.state
    exact coverage.returnDifferent (Option.some.inj (finished.pc.symm.trans pc))
  · intro c pre
    obtain ⟨copies,q,root,head⟩ := pre.state
    obtain ⟨after,nextCopies,run,⟨log,allowed,memory⟩,publication,post,less⟩ :=
      head.toHead.step_copy_effect head.reached (coverage.choices copies q root c head.reached head.toHead)
    have next := extend copies q root c nextCopies head.toHead publication head.tracked
    have preserved := frame copies q root c after nextCopies log head.toHead head.tracked publication allowed memory head.observation
    refine ⟨after,run,?_,less⟩
    rcases post with ⟨child,root,head,reached⟩ | finished
    · exact Or.inl ⟨⟨_,child,root,⟨head,reached,next,preserved⟩⟩⟩
    · exact Or.inr ⟨⟨_,⟨finished,next,preserved⟩⟩⟩

/-- The fixed-view API is the index-independent instance of the shared fold. -/
theorem run_copy_loop_observed {sp sources pl initial track observe}
    (coverage : CopyCoverage sp sources pl initial)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next)
    (frame : ∀ copies q root before after log, Head sp sources pl initial copies q root before → track copies →
      CopyEffect q root sp before log →
      after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log) →
      observe before → observe after) :
    Triple (ObservedAt sp sources pl initial track observe) (ObservedDone sp sources pl initial track observe) := by
  apply (run_copy_loop_indexed (observe := fun _ => observe) coverage extend
    (fun copies q root before after _ log head tracked _ allowed memory view =>
      frame copies q root before after log head tracked allowed memory view)).conseq
  · intro c pre
    obtain ⟨copies,q,root,head,reached,tracked⟩ := pre.operational
    exact ⟨⟨copies,q,root,⟨head,reached,tracked,pre.observation⟩⟩⟩
  · intro c post
    obtain ⟨copies,finished⟩ := post.state
    exact ⟨⟨copies,finished.toFinished,finished.tracked⟩,finished.observation⟩

/-- Original table-only API delegates to the observed fold. -/
theorem run_copy_loop_tracked {sp sources pl initial track}
    (coverage : CopyCoverage sp sources pl initial)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next) :
    Triple (TrackedAt sp sources pl initial track) (TrackedDone sp sources pl initial track) := by
  apply (run_copy_loop_observed (observe := fun _ => True) coverage extend
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)).conseq
  · intro c pre
    exact ⟨pre,True.intro⟩
  · intro c post
    exact post.operational

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
