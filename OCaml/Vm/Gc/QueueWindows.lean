import OCaml.Vm.Gc.Queue
import OCaml.Vm.Gc.ObservationFrame

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Reloc Primitives

/-- The queue's raw head and link observations are outside a collector
stage's write windows. The heap/native-stack ownership supplies these facts. -/
structure OutsideWindows (qs : List PendingCopy) (ws : List W) : Prop where
  root : OutWRange ws Layout.sym_oldify_todo_list 8
  cells : ∀ (i : Nat) (p : PendingCopy), qs[i]? = some p → ∀ (j : Nat) (cell : Nat × BitVec 64), (p.cells (next qs i))[j]? = some cell →
    OutWRange ws cell.1 8

theorem View.frame_windows {qs pl before after ws} (queue : View qs pl before)
    (outside : OutsideWindows qs ws) (memory : FrameOn ws before.σ.mem after.σ.mem) :
    View qs pl after := by
  refine ⟨(frame_word memory outside.root).trans queue.root, ?_⟩
  apply body_frame_words queue.links
  intro i p hp j cell hc
  exact frame_word memory (outside.cells i p hp j cell hc)

end OCaml.Vm.Gc.WorkQueue
