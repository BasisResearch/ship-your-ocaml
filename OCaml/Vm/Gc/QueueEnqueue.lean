import OCaml.Vm.Gc.Queue
import OCaml.Vm.Gc.Generated.Enqueue
import OCaml.Vm.Gc.Readback

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Sim Vsa.Machine Primitives

/-- Later stores preserve the new node, first field and caller's root.
These are finite footprint obligations for the allocator/collector geometry,
not a premise that allocation or collection is already correct. -/
structure EnqueueSeparated (q : PendingCopy) (root first next : BitVec 64) : Prop where
  rootPreserved : OutLRange ((Enqueue.effect q.source q.target root first next).drop 1) root.toNat 8
  header : OutLRange ((Enqueue.effect q.source q.target root first next).drop 2) (q.source - 8#64).toNat 8
  source : OutLRange ((Enqueue.effect q.source q.target root first next).drop 3) q.source.toNat 8
  firstPreserved : OutLRange ((Enqueue.effect q.source q.target root first next).drop 4) q.target.toNat 8
  todo : OutLRange ((Enqueue.effect q.source q.target root first next).drop 5) Layout.sym_oldify_todo_list 8

/-- Root/source separation already required by final root preservation also
protects the earlier read of the original source first field. -/
theorem EnqueueSeparated.sourceOutsideRoot {q root first next}
    (h : EnqueueSeparated q root first next) :
    OutLRange [(root.toNat, 8, q.target)] q.source.toNat 8 :=
  ⟨Or.symm h.rootPreserved.2.1, True.intro⟩

/-- New work-list node plus the caller root and first copied field. The
remaining fields intentionally stay pending for mopup. -/
structure EnqueuePost (q : PendingCopy) (qs : List PendingCopy) (pl : Place)
    (root first : BitVec 64) (c : Config) : Prop where
  queue : View (q :: qs) pl c
  root : word c root.toNat = q.target
  first : word c q.target.toNat = first

theorem EnqueuePost.memory_eq {q qs pl root first before after}
    (post : EnqueuePost q qs pl root first before) (memory : after.σ.mem = before.σ.mem) :
    EnqueuePost q qs pl root first after := by
  refine ⟨post.queue.memory_eq memory, ?_, ?_⟩
  · simpa only [word, memory] using post.root
  · simpa only [word, memory] using post.first

/-- The exact generated six-store effect installs the new intrusive head.
Allocator freshness and other queue links enter only as explicit footprint
facts; they remain to be supplied by the allocating call summary. -/
theorem enqueue {q qs pl c c' root size lds}
    (before : View qs pl c)
    (post : Enqueue.Post q.source q.target root size lds c.σ.mem c')
    (loadedNext : bytesVal .ld (lds.tail.headD []) = head qs)
    (separate : EnqueueSeparated q root (bytesVal .ld (lds.headD [])) (head qs))
    (tailOutside : LinksOutside qs
      (Enqueue.effect q.source q.target root (bytesVal .ld (lds.headD [])) (head qs))) :
    EnqueuePost q qs pl root (bytesVal .ld (lds.headD [])) c' := by
  have memory : c'.σ.mem = writeLog c.σ.mem
      (Enqueue.effect q.source q.target root (bytesVal .ld (lds.headD [])) (head qs)) := by
    rw [post.memory, Enqueue.writes, loadedNext]
  have read {i a v}
      (entry : (Enqueue.effect q.source q.target root (bytesVal .ld (lds.headD [])) (head qs))[i]? = some (a,8,v))
      (outside : OutLRange ((Enqueue.effect q.source q.target root
        (bytesVal .ld (lds.headD [])) (head qs)).drop (i+1)) a 8) : word c' a = v := by
    change bytesT c'.σ.mem a 8 = v
    rw [memory]
    exact word_writeLog_at _ _ i a v entry outside
  have node : PendingCopy.Links q (head qs) c' :=
    ⟨read (i := 1) rfl separate.header, read (i := 2) rfl separate.source,
      read (i := 5) rfl True.intro⟩
  refine ⟨⟨?_, body_cons (PendingCopy.of_links node)
    (body_frame_log before.links tailOutside memory)⟩,
    read (i := 0) rfl separate.rootPreserved, read (i := 3) rfl separate.firstPreserved⟩
  exact read (i := 4) rfl separate.todo

end OCaml.Vm.Gc.WorkQueue
