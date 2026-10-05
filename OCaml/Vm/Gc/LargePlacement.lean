import OCaml.Vm.Gc.FreePlacement
import OCaml.Vm.Gc.BestFitLarge
import OCaml.Vm.Gc.Readback
import OCaml.Vm.Primitives.MemoryFrame

/-!
# Placement of the least-large-block path

The proved large allocation path (`BestFitLarge.split`) splits the tree's
least block `bf_large_least`. If that block lies in `[lo, hi)` (`LeastIn`), the
returned block does too, the least pointer is unchanged, and the remnant stays
the least block, now ending where the returned block begins (`Split.placed`).
-/

namespace OCaml.Vm.Gc.BestFitLarge
open Vsa.Machine Vsa.Sim Primitives

/-- The least large free block lies in `[lo, hi)`. -/
def LeastIn (lo hi : Nat) (c : Config) : Prop := BestFitSplit.FreeIn lo hi (least c) c

/-- **The least-block split stays in the region.** The two stack stores miss
the region and the least pointer. -/
theorem Split.placed {sp : BitVec 64} {before after : Config} {lo hi : Nat}
    (post : Split sp before after) (inside : LeastIn lo hi before)
    (fits : (size sp before).toNat < (header before).toNat / 1024)
    (stackOut : ∀ e ∈ effect sp (size sp before) (header before), e.1 + e.2.1 ≤ lo ∨ hi ≤ e.1)
    (leastOut : OutLRange (splitEffect sp before) Layout.sym_bf_large_least 8) :
    lo ≤ (BestFitSplit.allocated (size sp before) (least before) before).toNat ∧
      (BestFitSplit.allocated (size sp before) (least before) before).toNat + 8 * ((size sp before).toNat + 1) ≤ hi ∧
      LeastIn lo (BestFitSplit.allocated (size sp before) (least before) before).toNat after := by
  have hl := inside.low
  have hh := inside.high
  have hr := inside.ram
  have sameLeast : least after = least before := by
    change bytesT after.σ.mem _ 8 = bytesT before.σ.mem _ 8
    rw [post.memory, bytesT_writeLog_out _ leastOut]
  have headerEq : BestFitSplit.header (least before) before = header before := rfl
  -- the source header survives the two stack stores
  have preparedHeader :
      BestFitSplit.header (least before) (prepared sp before) = header before := by
    change bytesT (writeLog before.σ.mem _) _ 8 = bytesT before.σ.mem _ 8
    rw [bytesT_writeLog_out _ (outLRange_of_forall fun e he => by
      rcases stackOut e he with h | h <;> omega)]
    rfl
  -- the remnant header is the split's last store
  have stored : word after (BestFitSplit.headerAddr (least before)).toNat =
      BestFitSplit.remnantHeader (BestFitSplit.route (size sp before) (header before))
        (BestFitSplit.delta (size sp before) (header before)) := by
    change bytesT after.σ.mem _ 8 = _
    rw [post.memory]
    apply word_writeLog_at _ _ 3 _ _ ?_ (by simp [splitEffect, effect, BestFitSplit.effect, OutLRange])
    simp [splitEffect, effect, BestFitSplit.effect, preparedHeader]
  have remnant := BestFitSplit.remnant_header (size sp before) (header before) fits
  rw [← stored] at remnant
  have r := BestFitSplit.allocated_toNat inside (Nat.le_of_lt fits)
  rw [headerEq] at r
  simp only [headerEq] at hh
  refine ⟨by omega, by omega, ?_⟩
  unfold LeastIn
  rw [sameLeast]
  refine ⟨hl, ?_, by omega⟩
  have size' : (BestFitSplit.header (least before) after).toNat / 1024 =
      (header before).toNat / 1024 - (size sp before).toNat - 1 := remnant.2
  rw [size', r]
  omega

end OCaml.Vm.Gc.BestFitLarge
