import OCaml.Vm.Gc.QueueAccess
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Gc.ObservationFrame

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Exactly the queue-head word is writable during a pop. -/
def popFootprint : List W := [⟨Layout.sym_oldify_todo_list, Layout.sym_oldify_todo_list + 8⟩]

theorem PopPost.loaded_regs {q qs pl before after} (post : PopPost q qs pl before after)
    (queue : View (q :: qs) pl before) :
    GHolds after.σ [(18,q.source),(19,q.target),(10,word before q.target.toNat)] := by
  have source : bytesVal .ld ((loads q before).headD []) = q.source := by
    change bytesVal .ld (read8 before.σ.mem Layout.sym_oldify_todo_list) = _
    rw [read8_value]; exact queue.root
  have target : bytesVal .ld ((loads q before).tail.headD []) = q.target := by
    change bytesVal .ld (read8 before.σ.mem q.source.toNat) = _
    rw [read8_value]; exact queue.first.target
  have pointers := post.machine.source_target
  rw [source, target] at pointers
  refine ⟨gholds_lookup _ pointers rfl, gholds_lookup _ pointers rfl, ?_, True.intro⟩
  simpa only [loads, List.tail_cons, List.headD_cons, read8_value, word] using post.machine.child_value

theorem PopPost.memory_effect {q qs pl before after} (post : PopPost q qs pl before after)
    (queue : View (q :: qs) pl before) :
    after.σ.mem = writeLog before.σ.mem [(Layout.sym_oldify_todo_list,8,head qs)] := by
  rw [post.machine.memory]
  change writeLog before.σ.mem (MopupPop.outcome _ _).log = _
  rw [MopupPop.queue_write, queue.loadedNext]

theorem PopPost.oldifyCode {q qs pl before after} (post : PopPost q qs pl before after)
    (queue : View (q :: qs) pl before) (code : Code.Caml_oldify_oneLoaded before.σ.mem) :
    Code.Caml_oldify_oneLoaded after.σ.mem := by
  rw [post.memory_effect queue]
  apply image_writeLog Code.caml_oldify_one_transport code
  intro e member
  have same := List.mem_singleton.mp member
  subst e
  change (0x80009cb4 : Nat) ≤ Layout.sym_oldify_todo_list
  decide

end OCaml.Vm.Gc.WorkQueue
