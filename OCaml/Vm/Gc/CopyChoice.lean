import OCaml.Vm.Gc.SingleTailLoop
import OCaml.Vm.Gc.SingleTailQueued

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives

/-- Data selecting either proved allocation route for a fresh child. The
constructors contain header/allocator observations, never a callee execution. -/
inductive QueueAllocation (q : PendingCopy) (root sp : BitVec 64) (c : Config) : BitVec 64 → List WEntry → Prop where
  | exactSize (domain : BitVec 64) (size tag : Nat)
      (even : ChildClassify.even (child q root c) = true)
      (range : YoungConditions q root domain c)
      (fresh : FreshChildConditions q root sp size tag c) :
      QueueAllocation q root sp c
        (Fresh.contextPayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        (AllocWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c))
  | large (domain : BitVec 64) (size tag : Nat)
      (even : ChildClassify.even (child q root c) = true)
      (range : YoungConditions q root domain c)
      (fresh : LargeFreshChildConditions q root sp size tag c) :
      QueueAllocation q root sp c
        (Fresh.contextLargePayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        (AllocLargeWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c))

/-- Execute the selected concrete allocator followed by queue insertion. -/
theorem QueueAllocation.run {q root sp c payload log qs pl}
    (allocation : QueueAllocation q root sp c payload log)
    (input : Input q root c) (stack : gprGet c.σ 2 = some sp)
    (constants : GHolds c.σ Fresh.loopConstants)
    (queue : QueuedChildConditions q root sp payload log qs pl c) :
    FnSummary pc (fun d => d = c) (QueuedChild q root sp payload log qs pl c) := by
  cases allocation with
  | exactSize domain size tag even range fresh =>
      exact prepare_enqueue_child input stack constants even range fresh queue
  | large domain size tag even range fresh =>
      exact prepare_enqueue_child_large input stack constants even range fresh queue

end OCaml.Vm.Gc.SingleField

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Primitives

/-- Ordinary single-field branches plus the real fresh multi-field child
exit. Queue ownership and original source membership remain data premises. -/
inductive CopyChoice (sp : BitVec 64) (sources : List (BitVec 64)) (copies : List PendingCopy)
    (pl : Place) (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop where
  | ordinary (choice : Choice sp sources copies q root c)
  | queued (payload : BitVec 64) (log : List WEntry) (qs : List PendingCopy)
      (allocation : SingleField.QueueAllocation q root sp c payload log)
      (queue : SingleField.QueuedChildConditions q root sp payload log qs pl c)
      (footprint : QueuedExitFootprint q root payload log qs copies sources c)
      (member : SingleField.child q root c ∈ sources)

/-- The concrete iteration adds the parent, and may also add its queued
child. This records the exact batch shape while preserving the old table. -/
inductive Publication (sources : List (BitVec 64)) (copies : List PendingCopy)
    (q : PendingCopy) (child : BitVec 64) : List PendingCopy → Prop where
  | parent : Publication sources copies q child (q :: copies)
  | queued (payload : BitVec 64) (member : child ∈ sources) :
      Publication sources copies q child (⟨child,payload⟩ :: q :: copies)

theorem Publication.retained {sources copies q child next}
    (publication : Publication sources copies q child next) : ∀ p ∈ copies, p ∈ next := by
  intro p member
  cases publication with
  | parent => exact List.mem_cons_of_mem _ member
  | queued payload childMember => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)

theorem Publication.bounded {sources copies q child next}
    (publication : Publication sources copies q child next)
    (bounded : ForwardingTable.Bounded copies sources) (member : q.source ∈ sources) :
    ForwardingTable.Bounded next sources := by
  cases publication with
  | parent => exact bounded.extend member
  | queued payload childMember => exact (bounded.extend member).extend childMember

/-- Concrete suffix alternatives after the parent's first three stores.
Queued exits retain allocation plus the child's six-store queue effect. -/
inductive CopyEffect (q : PendingCopy) (root sp : BitVec 64) (c : Config) : List WEntry → Prop where
  | ordinary {log} (effect : IterationLog q root sp c log) : CopyEffect q root sp c log
  | queued (payload : BitVec 64) (log : List WEntry) (qs : List PendingCopy)
      (allocation : SingleField.QueueAllocation q root sp c payload log) :
      CopyEffect q root sp c (log ++ Fresh.contextQueueEffect (SingleField.child q root c) payload q.target
        (Enqueue.prefixLog q.source q.target root ++ log) qs c)

/-- One iteration's published table and store log, from the same branch: an
ordinary branch publishes the parent; a queued exit publishes the parent and
its fresh child, and stores the selected allocation then the queue insertion. -/
inductive CopyStep (sources : List (BitVec 64)) (copies : List PendingCopy) (q : PendingCopy)
    (root sp : BitVec 64) (c : Config) : List PendingCopy → List WEntry → Prop where
  | ordinary {log} (effect : IterationLog q root sp c log) : CopyStep sources copies q root sp c (q :: copies) log
  | queued (payload : BitVec 64) (log : List WEntry) (qs : List PendingCopy)
      (allocation : SingleField.QueueAllocation q root sp c payload log)
      (member : SingleField.child q root c ∈ sources) :
      CopyStep sources copies q root sp c (⟨SingleField.child q root c,payload⟩ :: q :: copies)
        (log ++ Fresh.contextQueueEffect (SingleField.child q root c) payload q.target
          (Enqueue.prefixLog q.source q.target root ++ log) qs c)

theorem CopyStep.effect {sources copies q root sp c next log}
    (step : CopyStep sources copies q root sp c next log) : CopyEffect q root sp c log := by
  cases step with
  | ordinary effect => exact .ordinary effect
  | queued payload log qs allocation _ => exact .queued payload log qs allocation

theorem CopyStep.publication {sources copies q root sp c next log}
    (step : CopyStep sources copies q root sp c next log) :
    Publication sources copies q (SingleField.child q root c) next := by
  cases step with
  | ordinary => exact .parent
  | queued payload _ _ _ member => exact .queued payload member

/-- Execute one covered copying iteration, retaining its joint publication
and store log, and strict progress. All branches invoke concrete generated summaries. -/
theorem Head.step_copy_step {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c)
    (choice : CopyChoice sp sources copies pl q root c) :
    ∃ after nextCopies, Steps c after ∧
      (∃ log, CopyStep sources copies q root sp c nextCopies log ∧
        after.σ.mem = writeLog c.σ.mem (Enqueue.prefixLog q.source q.target root ++ log)) ∧
      ((∃ next root, Head sp sources pl initial nextCopies next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial nextCopies after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  cases choice with
  | ordinary choice =>
      obtain ⟨after,run,⟨log,allowed,memory⟩,post,less⟩ := head.step_effect reached choice
      exact ⟨after,_,run,⟨log,CopyStep.ordinary allowed,memory⟩,post,less⟩
  | queued payload log qs allocation queue footprint member =>
      obtain ⟨after,run,post⟩ := (allocation.run head.input head.stack head.constants queue).run c ⟨head.pc,rfl⟩
      have finish := head.finish_queued post footprint
      exact ⟨after,_,run,⟨_,CopyStep.queued payload log qs allocation member,
        by simpa only [List.append_assoc] using post.memory⟩,Or.inr finish.1,finish.2⟩

/-- The effect/publication view of `step_copy_step`. -/
theorem Head.step_copy_effect {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c)
    (choice : CopyChoice sp sources copies pl q root c) :
    ∃ after nextCopies, Steps c after ∧
      (∃ log, CopyEffect q root sp c log ∧
        after.σ.mem = writeLog c.σ.mem (Enqueue.prefixLog q.source q.target root ++ log)) ∧
      Publication sources copies q (SingleField.child q root c) nextCopies ∧
      ((∃ next root, Head sp sources pl initial nextCopies next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial nextCopies after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  obtain ⟨after,next,run,⟨log,step,memory⟩,post,less⟩ := head.step_copy_step reached choice
  exact ⟨after,next,run,⟨log,step.effect,memory⟩,step.publication,post,less⟩

/-- Published-table/rank interface hiding the concrete store log. -/
theorem Head.step_copy {sp sources pl initial copies q root c}
    (head : Head sp sources pl initial copies q root c) (reached : Steps initial c)
    (choice : CopyChoice sp sources copies pl q root c) :
    ∃ after nextCopies, Steps c after ∧ Publication sources copies q (SingleField.child q root c) nextCopies ∧
      ((∃ next root, Head sp sources pl initial nextCopies next root after ∧ Steps initial after) ∨
        Finished sp sources pl initial nextCopies after) ∧
      tailRemaining sources after < tailRemaining sources c := by
  obtain ⟨after,next,run,_,publication,post,less⟩ := head.step_copy_effect reached choice
  exact ⟨after,next,run,publication,post,less⟩

end OCaml.Vm.Gc.SingleTail
