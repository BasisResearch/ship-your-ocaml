import OCaml.Vm.Sim.ReverseCopyLog

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Sim

/-- The exact completed prefix of a forward word copy. -/
def forwardCopyLog (base : Nat) (words : List (BitVec 64)) (copied : Nat) : List WEntry :=
  (valueLog base words).take copied

theorem forward_copy_log_step (base : Nat) (words : List (BitVec 64)) (i : Nat)
    (bound : i < words.length) :
    forwardCopyLog base words (i + 1) = forwardCopyLog base words i ++ [(base + 8 * i, 8, words[i])] := by
  unfold forwardCopyLog
  rw [List.take_succ_eq_append_getElem (by rw [value_log_length]; exact bound), value_log_getElem base words i bound]

theorem forward_copy_log_complete (base : Nat) (words : List (BitVec 64)) :
    forwardCopyLog base words words.length = valueLog base words := by
  simp [forwardCopyLog, ← value_log_length base words]

/-- Separation of a whole observation range also separates any subrange. -/
theorem outLRange_subrange {log : List WEntry} {a n b width : Nat}
    (outside : OutLRange log a n) (lower : a ≤ b) (upper : b + width ≤ a + n) :
    OutLRange log b width := by
  induction log with
  | nil => trivial
  | cons entry log ih =>
    have here := outside.1
    exact ⟨by omega, ih outside.2⟩

/-- Every partial forward copy leaves the separated source snapshot unchanged. -/
theorem forward_copy_source_outside {source base copied i : Nat} {words : List (BitVec 64)}
    (separate : OutLRange (valueLog base words) source (8 * words.length)) (bound : i < words.length) :
    OutLRange (forwardCopyLog base words copied) (source + 8 * i) 8 := by
  apply outLRange_subrange (outLRange_sublist (List.take_sublist copied _) separate) <;> omega

end OCaml.Vm.Sim
