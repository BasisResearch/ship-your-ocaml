import OCaml.Vm.Gc.FreePlacement
import OCaml.Vm.Gc.SmallFreeList
import OCaml.Vm.Gc.AllocExact
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

namespace OCaml.Vm.Gc.FreeLists
open Vsa.Machine Vsa.Sim Primitives

/-- The small-list allocation result (`AllocExact.resultHeader`) is placed by
the list invariant alone: the head block lies in `[lo, hi)`. -/
theorem small_result_placed {lo hi : Nat} {size : BitVec 64} {c : Config}
    (lists : SmallListsIn lo hi c) (positive : 0 < size.toNat) (small : size.toNat ≤ Layout.bf_small_count)
    (nonnull : BestFitSmall.first size c ≠ 0) :
    lo ≤ (AllocExact.resultHeader size c).toNat ∧
      (AllocExact.resultHeader size c).toNat + 8 * (size.toNat + 1) ≤ hi := by
  have own := lists size.toNat positive small
  rw [show BitVec.ofNat 64 size.toNat = size by simp] at own
  have result : AllocExact.resultHeader size c =
      word c (BestFitSmall.slot size).toNat - BitVec.ofNat 64 Layout.header_bytes := rfl
  change word c (BestFitSmall.slot size).toNat ≠ 0 at nonnull
  rw [result]
  generalize word c (BestFitSmall.slot size).toNat = f at own nonnull ⊢
  cases own with
  | nil => exact absurd rfl nonnull
  | cons _ inside _ =>
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Layout.header_bytes]; omega)]
    simp only [Layout.header_bytes, BitVec.toNat_ofNat]
    omega

end OCaml.Vm.Gc.FreeLists
