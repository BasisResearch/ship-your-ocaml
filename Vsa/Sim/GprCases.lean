import Vsa.Sim.RegAccess

namespace Vsa.Sim
/-- The register numbers `1, …, 31`, decided once. -/
theorem gpr_range_fin : ∀ n : Fin 32, 1 ≤ n.val →
    n.val = 1 ∨ n.val = 2 ∨ n.val = 3 ∨ n.val = 4 ∨ n.val = 5 ∨ n.val = 6 ∨ n.val = 7 ∨ n.val = 8 ∨ n.val = 9 ∨ n.val = 10 ∨ n.val = 11 ∨ n.val = 12 ∨ n.val = 13 ∨ n.val = 14 ∨ n.val = 15 ∨ n.val = 16 ∨ n.val = 17 ∨ n.val = 18 ∨ n.val = 19 ∨ n.val = 20 ∨ n.val = 21 ∨ n.val = 22 ∨ n.val = 23 ∨ n.val = 24 ∨ n.val = 25 ∨ n.val = 26 ∨ n.val = 27 ∨ n.val = 28 ∨ n.val = 29 ∨ n.val = 30 ∨ n.val = 31 := by
  decide

theorem gpr_range (n : Nat) (h32 : n < 32) (h1 : 1 ≤ n) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 :=
  gpr_range_fin ⟨n, h32⟩ h1

/-- A property of the 31 general-purpose register numbers, checked once per register:
`gpr_cases n => tac` substitutes each literal `1, …, 31` for `n` (range hypotheses `1 ≤ n` and
`n ≤ 31` must be in context) and runs `tac` on each case. -/
syntax "gpr_cases " ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| gpr_cases $n:ident => $t:tacticSeq) => do
    let r := Lean.mkIdent `rfl
    `(tactic| (rcases gpr_range $n (by omega) (by omega) with $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r | $r <;> ($t)))

end Vsa.Sim
