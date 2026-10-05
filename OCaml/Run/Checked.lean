import OCaml.Run.Kernel

/-!
# Every-state facts of a finite run, by one evaluation

`checkAll f ok fuel c` walks the run of `f` from `c`, testing `ok` at every
visited state, and succeeds only if the run stops within `fuel`. One
`decide +kernel` of it gives `ok` at every state reachable from `c`
(`checkAll_reach`), without re-running each prefix. Instances: `Fits` and the
absence of `Forward_tag` blocks for a concrete program
(`OCaml/Programs/WhileMinChecks.lean`).
-/

namespace OCaml.Run

section
variable {C O : Type} (f : C → Except O C)

/-- `ok` holds at each state of the run from `c`, and the run stops within `fuel`. -/
def checkAll (ok : C → Bool) : Nat → C → Bool
  | 0, _ => false
  | n + 1, c => ok c && match f c with
    | .ok d => checkAll ok n d
    | .error _ => true

variable {f}

/-- A successful check covers every state the run reaches. -/
theorem checkAll_reach {ok : C → Bool} {fuel : Nat} {c : C} (h : checkAll f ok fuel c = true) :
    ∀ {n : Nat} {d : C}, iter f n c = .ok d → ok d = true := by
  induction fuel generalizing c with
  | zero => cases h
  | succ fuel ih =>
    intro n d hd
    simp only [checkAll, Bool.and_eq_true] at h
    cases n with
    | zero => cases hd; exact h.1
    | succ n =>
      cases hf : f c with
      | ok e =>
        rw [hf] at h
        exact ih h.2 (by simpa only [iter, hf, bind, Except.bind] using hd)
      | error o => simp only [iter, hf, bind, Except.bind] at hd; cases hd

end

end OCaml.Run
