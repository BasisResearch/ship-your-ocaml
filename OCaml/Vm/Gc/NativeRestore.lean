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

/-- Both decoded epilogues restore the same finite bank, in different
orders. Share the observation interface before identifying original values. -/
theorem StoreReturn.as_oldify {sp c} {after : Config}
    (holds : GHolds after.σ (StoreReturn.restored sp c)) :
    GHolds after.σ (OldifyReturn.restored sp c) := by
  have permutation : StoreReturn.slots.reverse.Perm OldifyReturn.slots.reverse := by decide
  exact (SaveBank.holds_permutation (List.Perm.cons (2,sp + OldifyReturn.frameSize)
    (permutation.map (fun cell => (cell.1,word c (sp + BitVec.ofNat 64 cell.2).toNat))))).mp holds

/-- Identify either restore order with the original oldify caller. -/
theorem StoreReturn.original_caller {R c} {after : Config}
    (saved : ∀ cell ∈ OldifyEntry.saves,
      word c (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1)
    (holds : GHolds after.σ (StoreReturn.restored (OldifyEntry.frameSp R) c)) :
    GHolds after.σ (OldifyEntry.callerRegs R) := by
  simpa only [OldifyEntry.restored_of_saved saved] using StoreReturn.as_oldify holds

end OCaml.Vm.Gc
