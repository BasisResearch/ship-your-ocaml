import OCaml.Vm.Gc.OldifyEntry
import OCaml.Vm.Gc.OldifyReturn
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Gc.SaveBank

namespace OCaml.Vm.Gc.OldifyEntry
open Vsa.Machine Vsa.Sim Primitives

/-- Every native-save address obeys the scalar store policy, independent
of the saved register values. Shared by complete-call and prefix images. -/
theorem saveLog_high {R slots}
    (windows : ∀ cell ∈ slots, WriteWindow (frameSp R + BitVec.ofNat 64 cell.2) 8) :
    ∀ e ∈ saveLog slots R, tohostAddr ≤ e.1 := by
  intro e member
  obtain ⟨cell,hc,rfl⟩ := List.mem_map.mp member
  have high := (windows cell hc).htif
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using
    Nat.le_trans (Nat.le_add_right Layout.sym_tohost 16) high

/-- A real high saved-slot RAM window rules out modular stack wraparound. -/
theorem Input.frame_bound {R c} (input : Input R c) :
    (frameSp R).toNat + maxSlot.2 + 8 ≤ 0x100000000 :=
  stack_bound (frameSp R) maxSlot.2 (by decide) (input.windows maxSlot max_mem)

theorem saved_address {R : Nat → BitVec 64}
    (bound : (frameSp R).toNat + maxSlot.2 + 8 ≤ 0x100000000)
    {cell : Nat × Nat} (member : cell ∈ saves) :
    (frameSp R + BitVec.ofNat 64 cell.2).toNat = (frameSp R).toNat + cell.2 :=
  stack_address (frameSp R) cell.2 maxSlot.2 bound (slots_bounded cell member)

/-- Every saved native register reads back from the actual prologue log.
Pairwise separation is a generated finite slot certificate, combined with
the concrete RAM window's no-wrap consequence. -/
theorem Post.saved {R before after} (post : Post R before after) (input : Input R before)
    (cell : Nat × Nat) (member : cell ∈ saves) :
    word after (frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 := by
  change bytesT after.σ.mem _ 8 = _
  rw [post.memory]
  exact SaveBank.read before.σ.mem (frameSp R) R saves maxSlot.2 input.frame_bound
    slots_bounded slots_separate cell member

/-- The epilogue register interface with the original caller's values. -/
def callerRegs (R : Nat → BitVec 64) : GRegs :=
  (2, R 2) :: OldifyReturn.slots.reverse.map (fun cell => (cell.1, R cell.1))

theorem Post.restored_caller {R before after} (post : Post R before after) (input : Input R before) :
    OldifyReturn.restored (frameSp R) after = callerRegs R := by
  have stack : frameSp R + OldifyReturn.frameSize = R 2 := by
    simp only [frameSp, BitVec.add_neg_eq_sub, BitVec.sub_add_cancel]
  unfold OldifyReturn.restored callerRegs
  rw [stack]
  congr 1
  apply List.map_congr_left
  intro cell member
  exact congrArg (fun w => (cell.1, w))
    (post.saved input cell (restore_slots cell (List.mem_reverse.mp member)))

theorem Post.returnWord {R before after} (post : Post R before after) (input : Input R before) :
    OldifyReturn.returnWord (frameSp R) after = R 1 := by
  exact post.saved input OldifyReturn.slots.head! (by decide)

end OCaml.Vm.Gc.OldifyEntry
