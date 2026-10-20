import OCaml.Vm.Boot.Startup.MemsetPair
import OCaml.Vm.Boot.Startup.ClearLoop
import Vsa.Sim.DlHeap
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

/-- A word-pair zeroing extent lies in the allocator arena and is aligned. -/
structure ZeroPairRegion (base count : Nat) : Prop where
  lower : heapStart ≤ base
  upper : base + 16 * count ≤ heapEnd
  aligned : base % 16 = 0

/-- A word-pair zeroing extent above the image (a global or the arena), aligned. -/
structure ZeroPairSpan (base count : Nat) : Prop where
  lower : Layout.sym_tohost + 16 ≤ base
  upper : base + 16 * count ≤ heapEnd
  aligned : base % 16 = 0

theorem ZeroPairRegion.span {base count : Nat} (r : ZeroPairRegion base count) : ZeroPairSpan base count :=
  ⟨by have := r.lower; unfold heapStart Layout.sym_tohost at *; omega, r.upper, r.aligned⟩

def pairCursor (base k : Nat) : BitVec 64 := BitVec.ofNat 64 (base + 16 * k)

theorem pairCursor_next (base k : Nat) : pairCursor base k + 16#64 = pairCursor base (k + 1) := by
  unfold pairCursor
  rw [← BitVec.ofNat_add]
  congr 1 <;> omega

theorem pairCursor_second (base k : Nat) :
    pairCursor base k + 8#64 = BitVec.ofNat 64 (base + 8 * (2 * k + 1)) := by
  unfold pairCursor
  rw [← BitVec.ofNat_add]
  congr 1 <;> omega

theorem ZeroPairSpan.clear {base count : Nat} (r : ZeroPairSpan base count) :
    ClearRegion base (2 * count) where
  lower := by have := r.lower; unfold Layout.sym_tohost at this; omega
  htif := r.lower
  upper := by have := r.upper; unfold heapEnd at this; omega
  aligned := by have := r.aligned; omega

theorem ZeroPairSpan.cursor_nat {base count k : Nat} (r : ZeroPairSpan base count)
    (bound : k ≤ count) : (pairCursor base k).toNat = base + 16 * k := by
  unfold pairCursor
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := r.upper
  unfold heapEnd at this
  omega

theorem ZeroPairSpan.window0 {base count k : Nat} (r : ZeroPairSpan base count)
    (bound : k < count) : WriteWindow (pairCursor base k) 8 := by
  have window := r.clear.window (k := 2 * k) (by omega)
  have addr : base + 8 * (2 * k) = base + 16 * k := by omega
  rw [addr] at window
  exact window

theorem ZeroPairSpan.window8 {base count k : Nat} (r : ZeroPairSpan base count)
    (bound : k < count) : WriteWindow (pairCursor base k + 8#64) 8 := by
  rw [pairCursor_second]
  exact r.clear.window (by omega)

theorem ZeroPairSpan.outside {base count k : Nat} (r : ZeroPairSpan base count)
    (bound : k < count) : ImageOutside (memsetPairLog (pairCursor base k)) := by
  have lower := r.lower
  have text : Image.textBase + Image.textSize ≤ Layout.sym_tohost + 16 := by decide
  have rodata : Image.rodataBase + Image.rodataSize ≤ Layout.sym_tohost + 16 := by decide
  have first := r.cursor_nat (Nat.le_of_lt bound)
  have second := r.clear.cursor_nat (k := 2 * k + 1) (by omega)
  constructor <;> simp only [memsetPairLog, OutLRange, first, pairCursor_second, second]
  all_goals exact ⟨Or.inl (by omega), Or.inl (by omega), trivial⟩

theorem ZeroPairRegion.clear {base count : Nat} (r : ZeroPairRegion base count) : ClearRegion base (2 * count) :=
  r.span.clear

theorem ZeroPairRegion.cursor_nat {base count k : Nat} (r : ZeroPairRegion base count) (bound : k ≤ count) :
    (pairCursor base k).toNat = base + 16 * k := r.span.cursor_nat bound

theorem ZeroPairRegion.window0 {base count k : Nat} (r : ZeroPairRegion base count) (bound : k < count) :
    WriteWindow (pairCursor base k) 8 := r.span.window0 bound

theorem ZeroPairRegion.window8 {base count k : Nat} (r : ZeroPairRegion base count) (bound : k < count) :
    WriteWindow (pairCursor base k + 8#64) 8 := r.span.window8 bound

theorem ZeroPairRegion.outside {base count k : Nat} (r : ZeroPairRegion base count) (bound : k < count) :
    ImageOutside (memsetPairLog (pairCursor base k)) := r.span.outside bound

/-- Pair stores reuse the existing exact zero-word memory effect. -/
theorem clearWords_pair (m : Std.ExtHashMap Nat (BitVec 8)) (base k : Nat) :
    clearWords m base (2 * (k + 1)) =
      writeLog (clearWords m base (2 * k))
        [(base + 16 * k, 8, 0#64), (base + 8 * (2 * k + 1), 8, 0#64)] := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, clearWords, clearWords, ← writeLog_append]
  rw [show base + 8 * (2 * k) = base + 16 * k by omega]
  rfl
end OCaml.Vm.Boot.Startup
