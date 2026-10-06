import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Sim

/-- A per-entry certificate constructs the inductive write-window predicate. -/
theorem log_in_windows_of_mem {windows : List W} {log : List WEntry}
    (inside : ∀ e ∈ log, InsideW windows e.1 e.2.1) : LogInW windows log := by
  induction log with
  | nil => trivial
  | cons entry log ih =>
    exact ⟨inside entry (by simp), ih (fun e he => inside e (by simp [he]))⟩

/-- A range outside every allowed window is disjoint from each allowed store. -/
theorem range_disjoint_inside {windows : List W} {a n address width : Nat}
    (outside : OutWRange windows a n) (inside : InsideW windows address width) :
    a + n ≤ address ∨ address + width ≤ a := by
  induction windows with
  | nil => exact False.elim inside
  | cons window windows ih =>
    rcases inside with here | tail
    · have separate := outside.1
      omega
    · exact ih outside.2 tail

/-- Derive subrange separation once from the write log's window certificate. -/
theorem outLRange_of_windows {windows : List W} {log : List WEntry} {a n : Nat}
    (inside : LogInW windows log) (outside : OutWRange windows a n) : OutLRange log a n := by
  induction log with
  | nil => trivial
  | cons entry log ih => exact ⟨range_disjoint_inside outside inside.1, ih inside.2⟩

/-- Separation of a whole observation range also separates any subrange. -/
theorem outLRange_subrange {log : List WEntry} {a n b width : Nat}
    (outside : OutLRange log a n) (lower : a ≤ b) (upper : b + width ≤ a + n) :
    OutLRange log b width := by
  induction log with
  | nil => trivial
  | cons entry log ih =>
    have here := outside.1
    exact ⟨by omega, ih outside.2⟩

end OCaml.Vm.Sim
