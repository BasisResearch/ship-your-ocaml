import OCaml.Vm.Sim.LogWindow

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim

/-- A word-store log indexed relative to a common frame base. -/
def indexedLog (base : Nat) (entries : List (Nat × BitVec 64)) : List WEntry :=
  entries.map fun e => (base + 8 * e.1, 8, e.2)

/-- Stores to distinct word indices cannot change a selected slot. -/
theorem indexed_log_outside {base index : Nat} {entries : List (Nat × BitVec 64)}
    (different : ∀ e ∈ entries, e.1 ≠ index) : OutLRange (indexedLog base entries) (base + 8 * index) 8 := by
  induction entries with
  | nil => trivial
  | cons entry entries ih =>
    have ne := different entry (by simp)
    refine ⟨by dsimp only; omega, ih (fun e he => different e (by simp [he]))⟩

/-- Readback is independent of store order when the word indices are unique.
Concrete frame families provide only their small index lists and membership facts. -/
theorem indexed_log_read (base : Nat) (entries : List (Nat × BitVec 64))
    (distinct : (entries.map Prod.fst).Nodup) (index : Nat) (value : BitVec 64)
    (selected : (index, value) ∈ entries) (memory : Std.ExtHashMap Nat (BitVec 8)) :
    bytesT (writeLog memory (indexedLog base entries)) (base + 8 * index) 8 = value := by
  induction entries generalizing memory with
  | nil => cases selected
  | cons entry entries ih =>
    have unique := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp selected with here | tail
    · subst entry
      apply word_writeLog_at memory (indexedLog base ((index, value) :: entries)) 0 _ _ rfl
      apply indexed_log_outside
      intro e member equal
      apply unique.1
      rw [← equal]
      exact List.mem_map_of_mem member
    · change bytesT (writeLog (applyW memory (base + 8 * entry.1, 8, entry.2))
        (indexedLog base entries)) (base + 8 * index) 8 = value
      exact ih unique.2 tail _

/-- Configuration-level readback of any indexed store in a unique-index log. -/
theorem indexed_stored {before after : Config} {base index : Nat} {value : BitVec 64}
    {entries : List (Nat × BitVec 64)} (distinct : (entries.map Prod.fst).Nodup)
    (selected : (index, value) ∈ entries)
    (memory : after.σ.mem = writeLog before.σ.mem (indexedLog base entries)) :
    word after (base + 8 * index) = value := by
  rw [word, memory]
  exact indexed_log_read base entries distinct index value selected before.σ.mem

/-- A bound on the finite index list certifies the whole frame write window. -/
theorem indexed_log_in {base count : Nat} {entries : List (Nat × BitVec 64)}
    (bound : ∀ e ∈ entries, e.1 < count) :
    LogInW [⟨base, base + 8 * count⟩] (indexedLog base entries) := by
  induction entries with
  | nil => trivial
  | cons entry entries ih =>
    have here := bound entry (by simp)
    refine ⟨Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩, ih (fun e he => bound e (by simp [he]))⟩

end OCaml.Vm.Sim
