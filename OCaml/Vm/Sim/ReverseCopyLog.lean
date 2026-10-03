import OCaml.Vm.Sim.ValueLog

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Already-copied high slots, in the machine's backward store order. -/
def reverseCopyLog (base : Nat) (words : List (BitVec 64)) (remaining : Nat) : List WEntry :=
  ((valueLog base words).drop remaining).reverse

theorem value_log_length (base : Nat) (words : List (BitVec 64)) :
    (valueLog base words).length = words.length := by
  simp [valueLog, indexedLog, valueEntries]

theorem value_log_getElem (base : Nat) (words : List (BitVec 64)) (i : Nat)
    (bound : i < words.length) :
    (valueLog base words)[i]'(by rw [value_log_length]; exact bound) = (base + 8 * i, 8, words[i]) := by
  simp [valueLog, indexedLog, valueEntries, List.getElem?_eq_getElem bound]

/-- Split the first initialized field from the generated forward copy. -/
theorem value_log_cons (a : Nat) (word : BitVec 64) (words : List (BitVec 64)) :
    valueLog a (word :: words) = (a, 8, word) :: valueLog (a + 8) words := by
  apply List.ext_getElem
  · simp only [value_log_length, List.length_cons]
  · intro i hi hj
    simp only [value_log_length, List.length_cons] at hi hj
    cases i with
    | zero => simp [value_log_getElem]
    | succ i =>
      have bound : i < words.length := by omega
      rw [value_log_getElem a (word :: words) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        value_log_getElem (a + 8) words i bound]
      congr 1
      omega

/-- One more native reverse-copy store extends the exact partial write log. -/
theorem reverse_copy_log_step (base : Nat) (words : List (BitVec 64)) (i : Nat)
    (bound : i < words.length) :
    reverseCopyLog base words i = reverseCopyLog base words (i + 1) ++ [(base + 8 * i, 8, words[i])] := by
  unfold reverseCopyLog
  rw [List.drop_eq_getElem_cons (by rw [value_log_length]; exact bound), List.reverse_cons,
    value_log_getElem base words i bound]

/-- The initial backward-copy log is empty. -/
theorem reverse_copy_log_initial (base : Nat) (words : List (BitVec 64)) :
    reverseCopyLog base words words.length = [] := by
  simp [reverseCopyLog, ← value_log_length base words]

/-- The completed backward copy uses the same unique-index readback certificate
as the forward copy; no commutation of concrete memory maps is needed. -/
theorem reverse_copy_log_words {pl : Place} {values : List Val} {words : List (BitVec 64)}
    {before after : Config} {base : Nat} (represented : ValueWords pl values words)
    (memory : after.σ.mem = writeLog before.σ.mem (reverseCopyLog base words 0)) :
    ∀ i v, values[i]? = some v → valWord pl v = some (word after (base + 8 * i)) := by
  apply represented.readback
  intro i w selected
  have written : after.σ.mem = writeLog before.σ.mem (indexedLog base (valueEntries words).reverse) := by
    simpa only [reverseCopyLog, valueLog, indexedLog, List.drop_zero, List.map_reverse] using memory
  apply indexed_stored _ _ written
  · simpa only [List.map_reverse, List.Nodup, List.pairwise_reverse, ne_comm] using value_entries_distinct words
  · exact List.mem_reverse.mpr (value_entries_selected selected)

/-- Every completed reverse-copy store is in the high suffix. -/
theorem reverse_copy_entry {base remaining : Nat} {words : List (BitVec 64)} {entry : WEntry}
    (member : entry ∈ reverseCopyLog base words remaining) :
    ∃ i, remaining ≤ i ∧ i < words.length ∧ entry.1 = base + 8 * i ∧ entry.2.1 = 8 := by
  obtain ⟨j, bound, selected⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mp member)
  have index : remaining + j < words.length := by
    rw [List.length_drop, value_log_length] at bound
    omega
  rw [List.getElem_drop, value_log_getElem base words (remaining + j) index] at selected
  subst entry
  exact ⟨remaining + j, by omega, index, rfl, rfl⟩

/-- The copied high suffix occupies its exact destination window. -/
theorem reverse_copy_log_in (base remaining : Nat) (words : List (BitVec 64)) :
    LogInW [⟨base + 8 * remaining, base + 8 * words.length⟩] (reverseCopyLog base words remaining) := by
  apply log_in_windows_of_mem
  intro entry member
  obtain ⟨i, lower, upper, address, width⟩ := reverse_copy_entry member
  rw [address, width]
  exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩

/-- Backward copying may overlap its source: completed high stores cannot alter
any unread low source slot when the destination starts at or above the source. -/
theorem reverse_copy_source_outside {source base remaining i : Nat} {words : List (BitVec 64)}
    (direction : source ≤ base) (unread : i < remaining) :
    OutLRange (reverseCopyLog base words remaining) (source + 8 * i) 8 := by
  apply outLRange_of_windows (reverse_copy_log_in base remaining words)
  exact ⟨Or.inl (by dsimp only; omega), trivial⟩

end OCaml.Vm.Sim
