import OCaml.Vm.Primitives.Write
import Vsa.Sim.InterpSpillReads

namespace OCaml.Vm.Gc
open Vsa.Sim Primitives

/-- Read back any full-word store whose suffix is disjoint, using the existing
write-log read64 theorem and the shared total-read bridge. -/
theorem word_writeLog_at (mem : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (i a : Nat) (v : BitVec 64)
    (entry : log[i]? = some (a, 8, v))
    (outside : OutLRange (log.drop (i + 1)) a 8) :
    bytesT (writeLog mem log) a 8 = v := by
  have read := read64_of_writeLog_at mem log i a v entry outside
  have value := execRetEpilogueWord_value _ _ v read
  change bytesVal .ld (read8 (writeLog mem log) a) = v at value
  simpa only [read8_value] using value

/-- Build a write-log footprint from its pointwise entry bounds. -/
theorem outLRange_of_forall {log : List WEntry} {a n : Nat}
    (outside : ∀ e ∈ log, a + n ≤ e.1 ∨ e.1 + e.2.1 ≤ a) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons e rest ih =>
      exact ⟨outside e (by simp), ih (fun x hx => outside x (by simp [hx]))⟩

/-- Every word in a pairwise-separated store bank reads back its saved value.
Native prologues instantiate this finite log law; no machine run is assumed. -/
theorem word_writeLog_cells (mem : Std.ExtHashMap Nat (BitVec 8))
    (cells : List (Nat × BitVec 64))
    (separate : cells.Pairwise (fun x y => x.1 + 8 ≤ y.1 ∨ y.1 + 8 ≤ x.1))
    {a : Nat} {v : BitVec 64} (member : (a, v) ∈ cells) :
    bytesT (writeLog mem (cells.map (fun (a,v) => (a,8,v)))) a 8 = v := by
  induction cells generalizing mem with
  | nil => simp at member
  | cons cell rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp separate
      rcases List.mem_cons.mp member with same | member
      · subst cell
        apply word_writeLog_at mem _ 0 a v rfl
        apply outLRange_of_forall
        intro e he
        obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp he
        exact head cell hc
      · exact ih (applyW mem (cell.1, 8, cell.2)) tail member

/-- Pointwise write containment supplies the reflected log's frame premise. -/
theorem logInW_of_forall {ws : List W} {log : List WEntry}
    (inside : ∀ e ∈ log, InsideW ws e.1 e.2.1) : LogInW ws log := by
  induction log with
  | nil => trivial
  | cons e log ih =>
    exact ⟨inside e (by simp), ih (fun e he => inside e (by simp [he]))⟩

end OCaml.Vm.Gc
