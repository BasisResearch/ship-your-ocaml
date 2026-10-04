import OCaml.Vm.Gc.ForwardingDomain
import OCaml.Vm.Gc.SingleTailState
import OCaml.Vm.Gc.SingleFieldNonYoung
import OCaml.Vm.Gc.LoopFold

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives LeanRV64DExecutable

def At (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial c : Config) : Prop :=
  ∃ copies q root, Head sp sources pl initial copies q root c ∧ Steps initial c

def Done (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial c : Config) : Prop :=
  ∃ copies, Finished sp sources pl initial copies c

/-- Data-only branch coverage for ordinary single-field chains. The heap
invariant must supply actual tag/range/header observations and separated
allocator footprints. No constructor assumes a machine execution. Other
object tags, multi-field copies and other allocator alternatives are open. -/
inductive Choice (sp : BitVec 64) (sources : List (BitVec 64)) (copies : List PendingCopy)
    (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop where
  | immediate
      (conditions : SingleField.ReturnConditions q root sp c)
      (footprint : ExitFootprint q root copies sources (StoreReturn.effect (SingleField.child q root c) q.target))
  | nonYoung (domain : BitVec 64)
      (even : ChildClassify.even (SingleField.child q root c) = true)
      (range : SingleField.RangeConditions q root domain c)
      (conditions : SingleField.ReturnGeometry q root sp c)
      (footprint : ExitFootprint q root copies sources (StoreReturn.effect (SingleField.child q root c) q.target))
  | forwarded (domain : BitVec 64)
      (even : ChildClassify.even (SingleField.child q root c) = true)
      (range : SingleField.YoungConditions q root domain c)
      (conditions : SingleField.ForwardedReturnConditions q root sp c)
      (footprint : ExitFootprint q root copies sources [(q.target.toNat,8,SingleField.forwardedValue q root c)])
  | exactSize (domain : BitVec 64) (tag : Nat)
      (even : ChildClassify.even (SingleField.child q root c) = true)
      (range : SingleField.YoungConditions q root domain c)
      (fresh : SingleField.FreshChildConditions q root sp 1 tag c)
      (conditions : SingleField.BackEdgeConditions q root sp
        (Fresh.contextPayload (SingleField.child q root c) q.target sp (SingleField.childHeader q root c) (SingleField.forwardedSnapshot q root c))
        copies sources (AllocWrapper.effect (SingleField.childAllocatorRegs q root sp c) (SingleField.forwardedSnapshot q root c)) c)
  | large (domain : BitVec 64) (tag : Nat)
      (even : ChildClassify.even (SingleField.child q root c) = true)
      (range : SingleField.YoungConditions q root domain c)
      (fresh : SingleField.LargeFreshChildConditions q root sp 1 tag c)
      (conditions : SingleField.BackEdgeConditions q root sp
        (Fresh.contextLargePayload (SingleField.child q root c) q.target sp (SingleField.childHeader q root c) (SingleField.forwardedSnapshot q root c))
        copies sources (AllocLargeWrapper.effect (SingleField.childAllocatorRegs q root sp c) (SingleField.forwardedSnapshot q root c)) c)

/-- Finite store alternatives for the ordinary single-field iteration.
These are concrete allocator/terminal logs, not arbitrary memory effects. -/
inductive IterationLog (q : PendingCopy) (root sp : BitVec 64) (c : Config) : List WEntry → Prop where
  | plain : IterationLog q root sp c (StoreReturn.effect (SingleField.child q root c) q.target)
  | forwarded : IterationLog q root sp c [(q.target.toNat,8,SingleField.forwardedValue q root c)]
  | exactSize : IterationLog q root sp c
      (AllocWrapper.effect (SingleField.childAllocatorRegs q root sp c) (SingleField.forwardedSnapshot q root c))
  | large : IterationLog q root sp c
      (AllocLargeWrapper.effect (SingleField.childAllocatorRegs q root sp c) (SingleField.forwardedSnapshot q root c))

/-- Each covered branch is executed by its proved concrete summary. A
back edge re-establishes Head; an exit restores the initial native bank.
Both strictly decrease the copying rank through the real parent prefix. -/
theorem Head.step_effect {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c) (choice : Choice sp sources copies q root c) :
    ∃ after, Steps c after ∧
      (∃ log, IterationLog q root sp c log ∧
        after.σ.mem = writeLog c.σ.mem (Enqueue.prefixLog q.source q.target root ++ log)) ∧
      ((∃ next root, Head sp sources pl initial (q :: copies) next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial (q :: copies) after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  cases choice with
  | immediate conditions footprint =>
      obtain ⟨after,run,post⟩ := (SingleField.return_immediate head.input head.stack conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_plain post) footprint
      exact ⟨after,run,⟨_,IterationLog.plain,post.memory⟩,Or.inr finish.1,finish.2⟩
  | nonYoung domain even range conditions footprint =>
      have domainRegister : gprGet c.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state) :=
        gholds_lookup _ head.constants rfl
      obtain ⟨after,run,post⟩ := (SingleField.return_even_nonYoung head.input head.stack domainRegister even range conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_plain post) footprint
      exact ⟨after,run,⟨_,IterationLog.plain,post.memory⟩,Or.inr finish.1,finish.2⟩
  | forwarded domain even range conditions footprint =>
      obtain ⟨after,run,post⟩ := (SingleField.return_young_forwarded head.input head.stack head.constants even range conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_forwarded post) footprint
      exact ⟨after,run,⟨_,IterationLog.forwarded,post.memory⟩,Or.inr finish.1,finish.2⟩
  | exactSize domain tag even range fresh conditions =>
      obtain ⟨after,run,post⟩ := (SingleField.backedge_exact head.input head.stack head.constants even range fresh head.table conditions).run c ⟨head.pc,rfl⟩
      exact ⟨after,run,⟨_,IterationLog.exactSize,post.allocated.memory⟩,Or.inl ⟨_,_,head.advance post conditions,reached.trans run⟩,post.decrease⟩
  | large domain tag even range fresh conditions =>
      obtain ⟨after,run,post⟩ := (SingleField.backedge_large head.input head.stack head.constants even range fresh head.table conditions).run c ⟨head.pc,rfl⟩
      exact ⟨after,run,⟨_,IterationLog.large,post.allocated.memory⟩,Or.inl ⟨_,_,head.advance post conditions,reached.trans run⟩,post.decrease⟩

/-- Exact published-list interface, hiding the concrete log when a client
only needs the operational invariant and rank. -/
theorem Head.step_exact {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c)
    (choice : Choice sp sources copies q root c) :
    ∃ after, Steps c after ∧
      ((∃ next root, Head sp sources pl initial (q :: copies) next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial (q :: copies) after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  obtain ⟨after,run,_,post,less⟩ := head.step_effect reached choice
  exact ⟨after,run,post,less⟩

/-- Public unindexed step interface, retaining the original loop API. -/
theorem Head.step {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c)
    (choice : Choice sp sources copies q root c) :
    ∃ after, Steps c after ∧ (At sp sources pl initial after ∨ Done sp sources pl initial after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  obtain ⟨after,run,post,less⟩ := head.step_exact reached choice
  refine ⟨after,run,?_,less⟩
  rcases post with ⟨next,root,head,reached⟩ | finished
  · exact Or.inl ⟨_,next,root,head,reached⟩
  · exact Or.inr ⟨_,finished⟩

/-- Coverage obligation for this ordinary single-field subloop. The global
heap/free-list invariant must produce Choice at each reachable head; this
record contains no callee-run or loop-execution premise. The native caller's
return site must be distinct from the internal forwarding-loop entry. -/
structure Coverage (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config) : Prop where
  returnDifferent : OldifyReturn.returnWord sp initial ≠ SingleField.pc
  choices : ∀ copies q root c, Steps initial c → Head sp sources pl initial copies q root c → Choice sp sources copies q root c

def TrackedAt (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (c : Config) : Prop :=
  ∃ copies q root, Head sp sources pl initial copies q root c ∧ Steps initial c ∧ track copies

def TrackedDone (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (c : Config) : Prop :=
  ∃ copies, Finished sp sources pl initial copies c ∧ track copies

/-- Add a memory observation to the operational loop entry. -/
structure ObservedAt (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : Config → Prop) (c : Config) : Prop where
  operational : TrackedAt sp sources pl initial track c
  observation : observe c

/-- The same memory observation at the actual native return. -/
structure ObservedDone (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (observe : Config → Prop) (c : Config) : Prop where
  operational : TrackedDone sp sources pl initial track c
  observation : observe c

/-- Shared machine loop fold with a memory frame. The frame law consumes
only the concrete store-log alternatives, never an assumed execution. Clients
prove it from Eqv transport and disjoint finite footprints. -/
theorem run_loop_observed {sp sources pl initial track observe} (coverage : Coverage sp sources pl initial)
    (extend : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies → track (q :: copies))
    (frame : ∀ copies q root before after log, Head sp sources pl initial copies q root before →
      track copies → IterationLog q root sp before log →
      after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root ++ log) →
      observe before → observe after) :
    Triple (ObservedAt sp sources pl initial track observe) (ObservedDone sp sources pl initial track observe) := by
  apply loop_to_exit (entry := SingleField.pc) (tailRemaining sources)
  · intro c pre
    obtain ⟨copies,q,root,head,_,_⟩ := pre.operational
    exact head.pc
  · intro c post pc
    obtain ⟨copies,finished,_⟩ := post.operational
    exact coverage.returnDifferent (Option.some.inj (finished.pc.symm.trans pc))
  · intro c pre
    obtain ⟨copies,q,root,head,reached,tracked⟩ := pre.operational
    obtain ⟨after,run,⟨log,allowed,memory⟩,post,less⟩ := head.step_effect reached (coverage.choices copies q root c reached head)
    have next := extend copies q root c head tracked
    have preserved := frame copies q root c after log head tracked allowed memory pre.observation
    refine ⟨after,run,?_,less⟩
    rcases post with ⟨child,root,head,reached⟩ | finished
    · exact Or.inl ⟨⟨_,child,root,head,reached,next⟩,preserved⟩
    · exact Or.inr ⟨⟨_,finished,next⟩,preserved⟩

/-- Published-list-only interface obtained by observing True. -/
theorem run_loop_tracked {sp sources pl initial track} (coverage : Coverage sp sources pl initial)
    (extend : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies → track (q :: copies)) :
    Triple (TrackedAt sp sources pl initial track) (TrackedDone sp sources pl initial track) := by
  apply (run_loop_observed (observe := fun _ => True) coverage extend
    (fun _ _ _ _ _ _ _ _ _ _ _ => True.intro)).conseq
  · intro c pre
    exact ⟨pre,True.intro⟩
  · intro c post
    exact post.operational

/-- Original untracked interface, instantiated from the shared fold without
changing its coverage or execution guarantees. -/
theorem run_loop {sp sources pl initial} (coverage : Coverage sp sources pl initial) :
    Triple (At sp sources pl initial) (Done sp sources pl initial) := by
  apply (run_loop_tracked (track := fun _ => True) coverage (fun _ _ _ _ _ _ => True.intro)).conseq
  · rintro c ⟨copies,q,root,head,reached⟩
    exact ⟨copies,q,root,head,reached,True.intro⟩
  · rintro c ⟨copies,finished,_⟩
    exact ⟨copies,finished⟩

/-- Entry-point summary from a concrete initial copying head. The original
native return and complete partial table follow from the machine loop fold. -/
theorem run_from_head {sp sources pl initial copies q root}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : Coverage sp sources pl initial) :
    FnSummary SingleField.pc (fun c => c = initial) (Done sp sources pl initial) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  exact run_loop coverage initial ⟨copies,q,root,head,Steps.refl initial⟩

/-- Entry-point summary preserving a chosen published-list property. -/
theorem run_from_head_tracked {sp sources pl initial copies q root track}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : Coverage sp sources pl initial) (tracked : track copies)
    (extend : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies → track (q :: copies)) :
    FnSummary SingleField.pc (fun c => c = initial) (TrackedDone sp sources pl initial track) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  exact run_loop_tracked coverage extend initial ⟨copies,q,root,head,Steps.refl initial,tracked⟩

/-- The actual loop's final map has exactly the forwarded source domain:
Complete is part of Finished, and Bounded is preserved by every new parent. -/
theorem run_from_head_bounded {sp sources pl initial copies q root}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : Coverage sp sources pl initial) (bounded : ForwardingTable.Bounded copies sources) :
    FnSummary SingleField.pc (fun c => c = initial)
      (TrackedDone sp sources pl initial (fun copies => ForwardingTable.Bounded copies sources)) := by
  apply run_from_head_tracked head coverage bounded
  intro copies q root c head bounded
  exact bounded.extend head.member

end OCaml.Vm.Gc.SingleTail
