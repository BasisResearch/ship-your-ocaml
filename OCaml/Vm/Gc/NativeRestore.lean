import OCaml.Vm.Gc.OldifySaved
import OCaml.Vm.Gc.StoreReturn

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- A native pin interface is independent of the order in which its saved
registers were restored. Shared across oldify's two decoded epilogues. -/
theorem SaveBank.holds_permutation {σ : MState} {xs ys : GRegs} (permutation : xs.Perm ys) :
    GHolds σ xs ↔ GHolds σ ys := by
  induction permutation with
  | nil => rfl
  | cons pin _ ih => exact and_congr Iff.rfl ih
  | swap a b tail => simp only [GHolds,and_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Identify the actual store/return bank with the original oldify caller,
using the same saved-word observations as the ordinary queue epilogue. -/
theorem StoreReturn.original_caller {R c} {after : Config}
    (saved : ∀ cell ∈ OldifyEntry.saves,
      word c (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1)
    (holds : GHolds after.σ (StoreReturn.restored (OldifyEntry.frameSp R) c)) :
    GHolds after.σ (OldifyEntry.callerRegs R) := by
  have stack : OldifyEntry.frameSp R + StoreReturn.frameSize = R 2 := by
    change (R 2 + -StoreReturn.frameSize) + StoreReturn.frameSize = R 2
    rw [BitVec.add_neg_eq_sub,BitVec.sub_add_cancel]
  have identified : StoreReturn.restored (OldifyEntry.frameSp R) c =
      (2,R 2) :: StoreReturn.slots.reverse.map (fun cell => (cell.1,R cell.1)) := by
    unfold StoreReturn.restored
    rw [stack]
    congr 1
    apply List.map_congr_left
    intro cell member
    have covered : ∀ cell ∈ StoreReturn.slots, cell ∈ OldifyEntry.saves := by decide
    exact congrArg (fun value => (cell.1,value)) (saved cell (covered cell (List.mem_reverse.mp member)))
  rw [identified] at holds
  have permutation : StoreReturn.slots.reverse.Perm OldifyReturn.slots.reverse := by decide
  exact (SaveBank.holds_permutation (List.Perm.cons (2,R 2)
    (permutation.map (fun cell => (cell.1,R cell.1))))).mp holds

end OCaml.Vm.Gc
