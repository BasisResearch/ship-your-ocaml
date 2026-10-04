import OCaml.Vm.Gc.AllocEntryAccess
import OCaml.Vm.Gc.Generated.AllocReturn
import OCaml.Vm.Gc.SaveBank

namespace OCaml.Vm.Gc.AllocEntry
open Vsa.Machine Vsa.Sim Primitives

/-- Native saves and the tag cell, all decoded by the prologue generator. -/
def saveCells := saves ++ [(11,tagOffset)]
def maxSave := saves.head!

theorem saveCells_bounded : ∀ cell ∈ saveCells, cell.2 ≤ maxSave.2 := by decide

theorem saveCells_separate : saveCells.Pairwise (fun x y => x.2 + 8 ≤ y.2 ∨ y.2 + 8 ≤ x.2) := by decide

def saveShape : SaveBank.Shape saveCells :=
  ⟨maxSave,by decide,by decide,saveCells_bounded,saveCells_separate⟩

theorem effect_bank (R : Nat → BitVec 64) : effect R = SaveBank.log (frameSp R) R saveCells := rfl

theorem Windows.frame_bound {R} (windows : Windows R) : (frameSp R).toNat + maxSave.2 + 8 ≤ 0x100000000 :=
  stack_bound (frameSp R) maxSave.2 (by decide) (windows.saved maxSave (by decide))

/-- Read any saved register or the saved tag from the exact prologue log. -/
theorem saved {R : Nat → BitVec 64} (mem : Std.ExtHashMap Nat (BitVec 8)) (windows : Windows R)
    (cell : Nat × Nat) (member : cell ∈ saveCells) :
    bytesT (writeLog mem (effect R)) (frameSp R + BitVec.ofNat 64 cell.2).toNat 8 = R cell.1 := by
  rw [effect_bank]
  exact saveShape.read mem (frameSp R) R (fun cell member => by
    simp only [saveCells,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member | rfl
    · exact windows.saved cell member
    · exact windows.tag) cell member

theorem restore_cells : ∀ cell ∈ AllocReturn.slots, cell ∈ saveCells := by decide

/-- Saved observations survive a separated intervening write log. -/
theorem saved_after {R : Nat → BitVec 64} (mem : Std.ExtHashMap Nat (BitVec 8)) (windows : Windows R)
    (later : List WEntry) (cell : Nat × Nat) (member : cell ∈ saveCells)
    (outside : OutLRange later (frameSp R + BitVec.ofNat 64 cell.2).toNat 8) :
    bytesT (writeLog (writeLog mem (effect R)) later)
      (frameSp R + BitVec.ofNat 64 cell.2).toNat 8 = R cell.1 := by
  rw [bytesT_writeLog_out _ outside]
  exact saved mem windows cell member

theorem effect_high {R} (windows : Windows R) :
    ∀ e ∈ effect R, Layout.sym_tohost + 16 ≤ e.1 := by
  rw [effect_bank]
  apply SaveBank.high
  intro cell member
  simp only [saveCells,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | rfl
  · exact windows.saved cell member
  · exact windows.tag


end OCaml.Vm.Gc.AllocEntry
