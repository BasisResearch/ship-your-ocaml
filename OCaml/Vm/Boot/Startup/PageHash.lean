import OCaml.Vm.Primitives.Read
import Vsa.Sim.RamReadBytes
namespace OCaml.Vm.Boot.Startup
open OCaml.Vm.Primitives Vsa.Sim

/-! The page table's hash slots as a pure model: slot `i` of the 2048-entry
table at `blk` is the word at `blk + 8 i`, zero when empty. Insertion by
linear probing terminates because an empty slot exists while the occupancy,
which equals the number of nonzero slots, is below 2048; probing from `h`
reaches any slot `e` after `(e - h) mod 2048` steps. -/

/-- Slot `i`'s word. -/
def pageSlot (m : Std.ExtHashMap Nat (BitVec 8)) (blk i : Nat) : BitVec 64 := bytesT m (blk + 8 * i) 8

/-- The number of nonzero slots. -/
def pageCount (m : Std.ExtHashMap Nat (BitVec 8)) (blk : Nat) : Nat :=
  ((List.range 2048).filter fun i => pageSlot m blk i != 0#64).length

/-- Fewer than 2048 nonzero slots leave an empty one. -/
theorem pageCount_empty {m : Std.ExtHashMap Nat (BitVec 8)} {blk : Nat} (room : pageCount m blk < 2048) :
    ∃ e, e < 2048 ∧ pageSlot m blk e = 0#64 := by
  apply Classical.byContradiction
  intro none
  have all : ((List.range 2048).filter fun i => pageSlot m blk i != 0#64) = List.range 2048 := by
    apply List.filter_eq_self.mpr
    intro i hi
    have lt : i < 2048 := List.mem_range.mp hi
    simp only [bne_iff_ne, ne_eq]
    exact fun zero => none ⟨i, lt, zero⟩
  unfold pageCount at room
  rw [all, List.length_range] at room
  exact Nat.lt_irrefl _ room

/-- The probe after `j` steps from `h`. -/
def probe (h j : Nat) : Nat := (h + j) % 2048

theorem probe_next (h j : Nat) : (probe h j + 1) % 2048 = probe h (j + 1) := by
  unfold probe; omega

/-- The distance from `h` to `e` along the probe sequence. -/
def probeDistance (h e : Nat) : Nat := (e + 2048 - h % 2048) % 2048

theorem probe_distance {h e : Nat} (he : e < 2048) : probe h (probeDistance h e) = e := by
  unfold probe probeDistance; omega

theorem probeDistance_lt (h e : Nat) : probeDistance h e < 2048 := by
  unfold probeDistance; omega
end OCaml.Vm.Boot.Startup
