import OCaml.Vm.Primitives.Read
import Vsa.Sim.RamReadBytes
import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.Write
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

/-- Writing slot `i` changes slot `i` only. -/
theorem pageSlot_write (m : Std.ExtHashMap Nat (BitVec 8)) (blk i j : Nat) (v : BitVec 64) :
    pageSlot (writeLog m [(blk + 8 * i, 8, v)]) blk j = if j = i then v else pageSlot m blk j := by
  unfold pageSlot
  split
  · subst_vars; exact word_writeLog _ _ _
  · rw [bytesT_writeLog_out _ (by simp only [OutLRange, and_true]; omega)]

/-- Raising one entry of a duplicate-free list from false to true adds one. -/
theorem filter_length_raise {l : List Nat} {P Q : Nat → Bool} {i : Nat} (nodup : l.Nodup) (mem : i ∈ l)
    (off : P i = false) (on : Q i = true) (same : ∀ j, j ≠ i → Q j = P j) :
    (l.filter Q).length = (l.filter P).length + 1 := by
  induction l with
  | nil => cases mem
  | cons a rest ih =>
    obtain ⟨notIn, nodupRest⟩ := List.nodup_cons.mp nodup
    by_cases ai : a = i
    · subst ai
      have keep : rest.filter Q = rest.filter P := by
        apply List.filter_congr
        intro j hj
        exact same j (fun e => notIn (e ▸ hj))
      simp [List.filter_cons, off, on, keep]
    · have inRest : i ∈ rest := by
        rcases List.mem_cons.mp mem with h | h
        · exact absurd h.symm ai
        · exact h
      have qa : Q a = P a := same a ai
      simp only [List.filter_cons, qa]
      split <;> simp [ih nodupRest inRest]

/-- Keeping an entry's truth keeps the count. -/
theorem filter_length_keep {l : List Nat} {P Q : Nat → Bool} (same : ∀ j, Q j = P j) :
    (l.filter Q).length = (l.filter P).length := by
  rw [List.filter_congr (fun j _ => same j)]

/-- Filling an empty slot adds one to the count. -/
theorem pageCount_fill {m : Std.ExtHashMap Nat (BitVec 8)} {blk i : Nat} {v : BitVec 64} (hi : i < 2048)
    (empty : pageSlot m blk i = 0#64) (nonzero : v ≠ 0#64) :
    pageCount (writeLog m [(blk + 8 * i, 8, v)]) blk = pageCount m blk + 1 := by
  unfold pageCount
  apply filter_length_raise List.nodup_range (List.mem_range.mpr hi)
  · simp [empty]
  · simp [pageSlot_write, nonzero]
  · intro j ne
    simp [pageSlot_write, ne]

/-- Overwriting an occupied slot with a nonzero word keeps the count. -/
theorem pageCount_update {m : Std.ExtHashMap Nat (BitVec 8)} {blk i : Nat} {v : BitVec 64}
    (occupied : pageSlot m blk i ≠ 0#64) (nonzero : v ≠ 0#64) :
    pageCount (writeLog m [(blk + 8 * i, 8, v)]) blk = pageCount m blk := by
  unfold pageCount
  apply filter_length_keep
  intro j
  rw [pageSlot_write]
  split
  · subst_vars; rw [bne_iff_ne.mpr nonzero, bne_iff_ne.mpr occupied]
  · rfl
end OCaml.Vm.Boot.Startup
