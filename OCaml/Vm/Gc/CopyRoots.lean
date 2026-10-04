import OCaml.Vm.Gc.CopyLoop
import OCaml.Vm.Gc.SingleTailRoots

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives

/-- Root ownership across every covered copying store alternative, including
allocation plus multi-field child insertion. This is a finite footprint
supplier, not a machine execution or a post-invariant assumption. -/
structure CopyRootFrame (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (cells : List SettledRoots.Cell) : Prop where
  outside : ∀ copies q root c log, Head sp sources pl initial copies q root c → track copies →
    CopyEffect q root sp c log → SettledRoots.Outside cells (Enqueue.prefixLog q.source q.target root ++ log)

/-- Completed roots survive the wider copying loop by transporting their
Eqv observations through each actual disjoint store log. -/
theorem run_copy_loop_roots {sp sources pl initial track cells}
    (coverage : CopyCoverage sp sources pl initial)
    (footprint : CopyRootFrame sp sources pl initial track cells)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next) :
    Triple (ObservedAt sp sources pl initial track (fun c => (SettledRoots.eqv cells).P pl 0 c))
      (ObservedDone sp sources pl initial track (fun c => (SettledRoots.eqv cells).P pl 0 c)) := by
  apply run_copy_loop_observed coverage extend
  intro copies q root before after log head tracked allowed memory view
  exact SettledRoots.frame view memory (footprint.outside copies q root before log head tracked allowed)

/-- Each concrete publication batch contains the current parent. -/
theorem Publication.parent_member {sources copies q child next}
    (publication : Publication sources copies q child next) : q ∈ next := by
  cases publication with
  | parent => exact List.mem_cons_self ..
  | queued payload member => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- The initial caller root remains represented through either scalar or
queued-child exit. The same RootReturned.represented theorem interprets it
under the final forwarding table. Ownership suppliers are still explicit. -/
theorem run_copy_from_head_root {sp sources pl initial copies q root}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : CopyCoverage sp sources pl initial)
    (first : ∀ log, CopyEffect q root sp initial log → SettledRoots.Footprint [] q root log)
    (later : CopyRootFrame sp sources pl initial (fun copies => q ∈ copies) [⟨root.toNat,q⟩]) :
    FnSummary SingleField.pc (fun c => c = initial) (RootReturned sp sources pl initial q root) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  obtain ⟨middle,nextCopies,run,⟨log,allowed,memory⟩,publication,post,_⟩ :=
    head.step_copy_effect (Steps.refl initial) (coverage.choices copies q root initial (Steps.refl initial) head)
  have empty : (SettledRoots.eqv []).P pl 0 initial := by intro cell member; simp at member
  have written := SettledRoots.publish empty memory (first log allowed)
  have member := publication.parent_member
  have ready : ObservedAt sp sources pl initial (fun copies => q ∈ copies)
      (fun c => (SettledRoots.eqv [⟨root.toNat,q⟩]).P pl 0 c) middle ∨
      ObservedDone sp sources pl initial (fun copies => q ∈ copies)
      (fun c => (SettledRoots.eqv [⟨root.toNat,q⟩]).P pl 0 c) middle := by
    rcases post with ⟨next,nextRoot,nextHead,reached⟩ | finished
    · exact Or.inl ⟨⟨_,next,nextRoot,nextHead,reached,member⟩,written⟩
    · exact Or.inr ⟨⟨_,finished,member⟩,written⟩
  have extend : ∀ copies next root c result, Head sp sources pl initial copies next root c →
      Publication sources copies next (SingleField.child next root c) result → q ∈ copies → q ∈ result := by
    intro copies next root c result head publication member
    exact publication.retained q member
  obtain ⟨after,rest,result⟩ :=
    (Triple.cases (run_copy_loop_roots coverage later extend) Triple.rfl) middle ready
  exact ⟨after,run.trans rest,⟨result⟩⟩

end OCaml.Vm.Gc.SingleTail
