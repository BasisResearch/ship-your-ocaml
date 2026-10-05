import OCaml.Vm.Gc.CopyLoop
import OCaml.Vm.Gc.SourceObjects

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Vsa.Logic Primitives

/-- Heap ownership supplies disjoint header/payload windows for every
source left unforwarded by an iteration. The newly published source batch
may be overwritten. This is a finite log-footprint obligation only. -/
structure SourceFrame (sp : BitVec 64) (sources : List (BitVec 64)) (pl : Place) (initial : Config)
    (track : List PendingCopy → Prop) (objects : List SourceObjects.Entry) : Prop where
  outside : ∀ copies q root c next log, Head sp sources pl initial copies q root c → track copies →
    CopyStep sources copies q root sp c next log →
    SourceObjects.Outside objects next (Enqueue.prefixLog q.source q.target root ++ log)

/-- Preserve the typed original shape of every as-yet-unforwarded source
through actual copying iterations, while the published-table index grows. -/
theorem run_copy_loop_sources {sp sources pl cp initial track objects}
    (coverage : CopyCoverage sp sources pl initial)
    (footprint : SourceFrame sp sources pl initial track objects)
    (extend : ∀ copies q root c next, Head sp sources pl initial copies q root c →
      Publication sources copies q (SingleField.child q root c) next → track copies → track next) :
    Triple (IndexedAt sp sources pl initial track (fun copies c => SourceObjects.View objects copies pl cp c))
      (IndexedDone sp sources pl initial track (fun copies c => SourceObjects.View objects copies pl cp c)) := by
  apply run_copy_loop_indexed coverage extend
  intro copies q root before after next log head tracked step memory view
  exact view.frame step.publication.retained memory
    (footprint.outside copies q root before next log head tracked step)

/-- Every fresh head described in the original source metadata still has
its original object representation in the current machine memory. -/
theorem IndexedHead.source_object {sp sources pl cp initial track objects copies q root c entry}
    (head : IndexedHead sp sources pl initial track (fun copies c => SourceObjects.View objects copies pl cp c) copies q root c)
    (member : entry ∈ objects) (same : entry.source = q.source) :
    ObjAt c pl cp q.source.toNat entry.object := by
  have fresh : word c (entry.source - 8#64).toNat ≠ 0 := by simpa only [same] using head.fresh
  simpa only [same] using head.observation.fresh_object head.table member fresh

/-- Whole copying loop with complete/bounded table and preservation of all
remaining source objects, without assuming an empty nursery. Full copied
object/queue closure and the ownership supplier remain separate obligations. -/
theorem run_copy_from_head_sources {sp sources pl cp initial copies q root objects}
    (head : Head sp sources pl initial copies q root initial)
    (coverage : CopyCoverage sp sources pl initial)
    (bounded : ForwardingTable.Bounded copies sources)
    (view : SourceObjects.View objects copies pl cp initial)
    (footprint : SourceFrame sp sources pl initial (fun copies => ForwardingTable.Bounded copies sources) objects) :
    FnSummary SingleField.pc (fun c => c = initial)
      (IndexedDone sp sources pl initial (fun copies => ForwardingTable.Bounded copies sources)
        (fun copies c => SourceObjects.View objects copies pl cp c)) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  apply run_copy_loop_sources coverage footprint ?_ initial
    ⟨⟨copies,q,root,⟨head,Steps.refl initial,bounded,view⟩⟩⟩
  intro copies q root c next head publication bounded
  exact publication.bounded bounded head.member

end OCaml.Vm.Gc.SingleTail
