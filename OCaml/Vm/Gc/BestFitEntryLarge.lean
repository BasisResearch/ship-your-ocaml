import OCaml.Vm.Gc.BestFitEntrySmall
import OCaml.Vm.Gc.BestFitLargeComplete

/-! The old small representation does not supply the zero-bitmap branch.
The separate bounded refinement repairs native filtering. The counterexample
remains an entry-interface witness, not a native reachability claim. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- No suitable class supplies the actual missing slot, without restricting
the lists below the request. The bitmap obligation remains separate. -/
theorem EntryInput.missing_of_noSuitable {R lists c} (input : EntryInput R lists c)
    (small : (R 10).toNat ≤ Layout.bf_small_count)
    (noSuitable : ∀ s, (R 10).toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []) :
    MissingInput R c :=
  input.missing_input small (noSuitable _ (Nat.le_refl _) small)

/-- Full native SLLW mask, including request sixteen. -/
theorem mask_small_bit {request : BitVec 64} (small : request.toNat ≤ 16)
    {j : Nat} (low : j < 32) :
    (mask request).getLsbD j = decide (request.toNat ≤ j) := by
  have table : ∀ n < 17, ∀ i < 32,
      (mask (BitVec.ofNat 64 n)).getLsbD i = decide (n ≤ i) := by decide
  simpa using table request.toNat (by omega) j low

/-- The real LW sign extension has no high bits under the bounded refinement. -/
theorem bounded_bitmap_high {m} (bounded : BfShape.BoundedBitmap m)
    {j : Nat} (high : 16 ≤ j) (width : j < 64) :
    (bytesVal .lw (read4 m Layout.sym_bf_small_map)).getLsbD j = false := by
  have bits : ∀ i, 16 ≤ i → (BfShape.mapBits m).getLsbD i = false := by
    intro i hi
    have eq : 16+(i-16) = i := by omega
    simpa only [eq] using BfShape.BoundedBitmap.high_iff.mp bounded (i-16)
  simp only [read4_value,Functions.sign_extend,Sail.BitVec.signExtend,BitVec.getLsbD_signExtend]
  change (decide (j < 64) && if j < 32 then (BfShape.mapBits m).getLsbD j else
    (BfShape.mapBits m).msb) = false
  rw [show decide (j < 64) = true from by simp [width],Bool.true_and]
  split
  · exact bits j high
  · simpa only [BitVec.msb_eq_getLsbD_last] using bits 31 (by decide)

/-- Original representation plus high-bit refinement supplies the exact native
LW/SLLW/AND zero test. Lower classes may be nonempty. -/
theorem filtered_of_noSuitable {m lists request}
    (repr : BfShape.BoundedSmallRepresentation m lists) (positive : 1 ≤ request.toNat)
    (small : request.toNat ≤ Layout.bf_small_count)
    (noSuitable : ∀ s, request.toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []) :
    filtered request (bytesVal .lw (read4 m Layout.sym_bf_small_map)) = 0#64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j width
  rw [filtered,BitVec.getLsbD_and,BitVec.getLsbD_zero]
  by_cases low : j < 16
  · rw [mask_small_bit small (by omega)]
    by_cases selected : request.toNat ≤ j
    · have empty := noSuitable (j+1) (by omega) (by change j+1 ≤ 16; omega)
      have clear : (BfShape.mapBits m).getLsbD j = false := by
        have consistent := repr.map (j+1) (by omega) (by change j+1 ≤ 16; omega)
        simp only [Nat.add_sub_cancel,empty,ne_self_iff_false,iff_false] at consistent
        exact Bool.eq_false_iff.mpr consistent
      simp only [read4_value,Functions.sign_extend,Sail.BitVec.signExtend,BitVec.getLsbD_signExtend]
      change ((decide (j < 64) && if j < 32 then (BfShape.mapBits m).getLsbD j else
        (BfShape.mapBits m).msb) && decide (request.toNat ≤ j)) = false
      simp only [if_pos (show j < 32 by omega),clear,Bool.and_false,Bool.false_and]
    · simp [selected]
  · rw [bounded_bitmap_high repr.bounded (by omega) width]

/-- All list slots are zero, but the first unrepresented bitmap bit is set. -/
def highBitmapMemory : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog ∅ [(Layout.sym_bf_small_map,4,0x10000#64)]

theorem highBitmapMemory_bits : BfShape.mapBits highBitmapMemory = 0x10000#32 :=
  word32_writeLog _ _ _

/-- The interface witness is excluded precisely by the new named refinement. -/
theorem highBitmapMemory_not_bounded : ¬ BfShape.BoundedBitmap highBitmapMemory := by
  rw [BfShape.BoundedBitmap,highBitmapMemory_bits]
  decide

theorem highBitmapMemory_slot {s : Nat} (small : s ≤ Layout.bf_small_count) :
    bytesT highBitmapMemory (BfShape.slot s).toNat 8 = 0#64 := by
  rw [highBitmapMemory,bytesT_writeLog_out _ (show
    OutLRange [(Layout.sym_bf_small_map,4,0x10000#64)] (BfShape.slot s).toNat 8 from by
      rw [BfShape.slot_toNat s small]
      exact ⟨Or.inr (by simp only [Layout.sym_bf_small_map,Layout.sym_bf_small_fl]; omega),True.intro⟩)]
  simp [bytesT]

/-- Even the stronger all-empty family satisfies every current component.
The witness is used only to refute a purported representation-only supplier. -/
theorem highBitmapMemory_representation :
    BfShape.SmallRepresentation highBitmapMemory (fun _ => []) := by
  refine ⟨⟨?_,?_,?_⟩,⟨?_⟩,?_,BfShape.SmallPhysical.empty⟩
  · intro s _ small
    exact highBitmapMemory_slot small
  · intro s lo hi b member
    simp at member
  · intro s lo hi b member
    simp at member
  · intro s lo hi b member
    simp at member
  · intro s positive small
    have low : ∀ s < 17, 1 ≤ s → (0x10000#32).getLsbD (s-1) = false := by decide
    rw [highBitmapMemory_bits,low s (by change s ≤ 16 at small; omega) positive]
    simp

/-- The actual LW and SLLW/AND filter retains bit 16 for request one. -/
theorem highBitmapMemory_filtered :
    filtered (1#64) (bytesVal .lw (read4 highBitmapMemory Layout.sym_bf_small_map)) = 0x10000#64 := by
  rw [read4_value,show bytesT highBitmapMemory Layout.sym_bf_small_map 4 = 0x10000#32 from
    highBitmapMemory_bits]
  decide

/-- A named entry-interface counterexample, including the actual native
bitmap expression. No assumption about a large tree can repair this read. -/
structure ZeroBitmapObstruction (m : Std.ExtHashMap Nat (BitVec 8))
    (lists : Nat → List (BitVec 64)) (request : BitVec 64) : Prop where
  representation : BfShape.SmallRepresentation m lists
  positive : 1 ≤ request.toNat
  small : request.toNat ≤ Layout.bf_small_count
  noSuitable : ∀ s, request.toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []
  filteredNonzero : filtered request (bytesVal .lw (read4 m Layout.sym_bf_small_map)) ≠ 0#64

theorem highBitmapMemory_obstruction :
    ZeroBitmapObstruction highBitmapMemory (fun _ => []) (1#64) :=
  ⟨highBitmapMemory_representation,by decide,by decide,fun _ _ _ => rfl,
    by rw [highBitmapMemory_filtered]; decide⟩

/-- The requested zero-bitmap derivation is false for the current shared
representation, even with every small list empty and a positive small request. -/
theorem no_representation_only_zero_bitmap :
    ¬ (∀ (m : Std.ExtHashMap Nat (BitVec 8)) (lists : Nat → List (BitVec 64)) (request : BitVec 64),
      BfShape.SmallRepresentation m lists → 1 ≤ request.toNat →
      request.toNat ≤ Layout.bf_small_count →
      (∀ s, request.toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []) →
      filtered request (bytesVal .lw (read4 m Layout.sym_bf_small_map)) = 0#64) := by
  intro producer
  have witness := highBitmapMemory_obstruction
  exact witness.filteredNonzero (producer _ _ _ witness.representation witness.positive
    witness.small witness.noSuitable)

end OCaml.Vm.Gc.BestFitFallback
