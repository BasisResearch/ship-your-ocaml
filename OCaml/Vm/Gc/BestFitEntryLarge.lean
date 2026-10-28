import OCaml.Vm.Gc.BestFitEntrySmall
import OCaml.Vm.Gc.BestFitLargeComplete

/-! The current small representation does not supply the zero-bitmap branch.
This bounded counterexample concerns the entry interface, not reachability
from native initialization. No new initialization premise is a producer. -/
namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- No suitable class supplies the actual missing slot, without restricting
the lists below the request. The bitmap obligation remains separate. -/
theorem EntryInput.missing_of_noSuitable {R lists c} (input : EntryInput R lists c)
    (small : (R 10).toNat ≤ Layout.bf_small_count)
    (noSuitable : ∀ s, (R 10).toNat ≤ s → s ≤ Layout.bf_small_count → lists s = []) :
    MissingInput R c :=
  input.missing_input small (noSuitable _ (Nat.le_refl _) small)

/-- All list slots are zero, but the first unrepresented bitmap bit is set. -/
def highBitmapMemory : Std.ExtHashMap Nat (BitVec 8) :=
  writeLog ∅ [(Layout.sym_bf_small_map,4,0x10000#64)]

theorem highBitmapMemory_bits : BfShape.mapBits highBitmapMemory = 0x10000#32 :=
  word32_writeLog _ _ _

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
