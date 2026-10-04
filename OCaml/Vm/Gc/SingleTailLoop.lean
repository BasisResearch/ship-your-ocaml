import OCaml.Vm.Gc.ForwardingDomain
import OCaml.Vm.Gc.SingleTailState
import OCaml.Vm.Gc.SingleFieldNonYoung
import Vsa.Sim.DeriveLoop

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

/-- Each covered branch is executed by its proved concrete summary. A
back edge re-establishes Head; an exit restores the initial native bank.
Both strictly decrease the copying rank through the real parent prefix. -/
theorem Head.step_exact {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c) (choice : Choice sp sources copies q root c) :
    ∃ after, Steps c after ∧
      ((∃ next root, Head sp sources pl initial (q :: copies) next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial (q :: copies) after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  cases choice with
  | immediate conditions footprint =>
      obtain ⟨after,run,post⟩ := (SingleField.return_immediate head.input head.stack conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_plain post) footprint
      exact ⟨after,run,Or.inr finish.1,finish.2⟩
  | nonYoung domain even range conditions footprint =>
      have domainRegister : gprGet c.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state) :=
        gholds_lookup _ head.constants rfl
      obtain ⟨after,run,post⟩ := (SingleField.return_even_nonYoung head.input head.stack domainRegister even range conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_plain post) footprint
      exact ⟨after,run,Or.inr finish.1,finish.2⟩
  | forwarded domain even range conditions footprint =>
      obtain ⟨after,run,post⟩ := (SingleField.return_young_forwarded head.input head.stack head.constants even range conditions).run c ⟨head.pc,rfl⟩
      have finish := head.finish (returned_forwarded post) footprint
      exact ⟨after,run,Or.inr finish.1,finish.2⟩
  | exactSize domain tag even range fresh conditions =>
      obtain ⟨after,run,post⟩ := (SingleField.backedge_exact head.input head.stack head.constants even range fresh head.table conditions).run c ⟨head.pc,rfl⟩
      exact ⟨after,run,Or.inl ⟨_,_,head.advance post conditions,reached.trans run⟩,post.decrease⟩
  | large domain tag even range fresh conditions =>
      obtain ⟨after,run,post⟩ := (SingleField.backedge_large head.input head.stack head.constants even range fresh head.table conditions).run c ⟨head.pc,rfl⟩
      exact ⟨after,run,Or.inl ⟨_,_,head.advance post conditions,reached.trans run⟩,post.decrease⟩

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

/-- One machine loop fold for any property of the published list preserved
by its actual one-parent extension. The extension premise is a list/data
law; concrete executions come exclusively from Head.step_exact. -/
theorem run_loop_tracked {sp sources pl initial track} (coverage : Coverage sp sources pl initial)
    (extend : ∀ copies q root c, Head sp sources pl initial copies q root c → track copies → track (q :: copies)) :
    Triple (TrackedAt sp sources pl initial track) (TrackedDone sp sources pl initial track) := by
  let Inv := fun c => TrackedAt sp sources pl initial track c ∨ TrackedDone sp sources pl initial track c
  let Branch := fun c => PCAt SingleField.pc c
  have body : ∀ n, Triple (fun c => Inv c ∧ Branch c ∧ tailRemaining sources c = n)
      (fun c => Inv c ∧ tailRemaining sources c < n) := by
    intro n c pre
    rcases pre with ⟨inv,branch,rank⟩
    rcases inv with ⟨copies,q,root,head,reached,tracked⟩ | ⟨copies,finished,tracked⟩
    · obtain ⟨after,run,post,less⟩ := head.step_exact reached (coverage.choices copies q root c reached head)
      have next := extend copies q root c head tracked
      refine ⟨after,run,?_,by omega⟩
      rcases post with ⟨child,root,head,reached⟩ | finished
      · exact Or.inl ⟨_,child,root,head,reached,next⟩
      · exact Or.inr ⟨_,finished,next⟩
    · exact False.elim (coverage.returnDifferent (Option.some.inj (finished.pc.symm.trans branch)))
  apply (loopFromBody (I := Inv) (B := Branch) (tailRemaining sources) body).conseq
  · intro c head
    exact Or.inl head
  · intro c post
    rcases post with ⟨inv,exit⟩
    rcases inv with ⟨copies,q,root,head,reached,tracked⟩ | finished
    · exact False.elim (exit head.pc)
    · exact finished

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
