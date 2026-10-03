import OCaml.Vm.Gc.PopFirstPayload
import OCaml.Vm.Gc.ScanFootprint

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives

/-- Queue head, native saves and the copied object's first slot are the
only writable regions before suffix setup. -/
def firstFootprint (R : Nat → BitVec 64) (q : PendingCopy) : List W :=
  popFootprint ++ [MopupCall.nativeWindow R, ⟨q.target.toNat,q.target.toNat + 8⟩]

/-- The exact prefix log is contained in its three geometric regions.
The native extent comes from the generated save slots and their RAM window. -/
theorem first_log_inside {R domain q qs c} (ready : FirstReady R domain q c) :
    LogInW (firstFootprint R q) ([(Layout.sym_oldify_todo_list,8,head qs)] ++ firstEffect R q c) := by
  have bound : (OldifyEntry.frameSp R).toNat + OldifyEntry.maxSlot.2 + 8 ≤ 0x100000000 :=
    stack_bound (OldifyEntry.frameSp R) OldifyEntry.maxSlot.2 (by decide)
      (ready.windows OldifyEntry.maxSlot OldifyEntry.max_mem)
  apply logInW_of_forall
  intro e member
  rcases List.mem_append.mp member with headWrite | callWrite
  · have same := List.mem_singleton.mp headWrite
    subst e
    exact Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩
  · have cell := MopupCall.effect_entry_of_bound (R := FirstCall.linked (FirstField.args (firstRegs R q c)))
      (c := c) (b := q.target.toNat) (i := 0) bound (by rfl) callWrite
    rcases cell with native | ⟨address,width⟩
    · exact Or.inr (Or.inl native)
    · right; right; left
      rw [address, width]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem PopFirstPost.memory_frame {R domain q qs pl before after}
    (post : PopFirstPost R q qs pl before after) (ready : FirstReady R domain q before) :
    FrameOn (firstFootprint R q) before.σ.mem after.σ.mem := by
  rw [post.memory]
  exact frameOn_writeLog _ _ _ (first_log_inside ready)

end OCaml.Vm.Gc.WorkQueue
