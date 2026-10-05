import OCaml.Bytecode.Semantics

/-!
# Extra-argument counts fit a native word

`caml_interprete` keeps `extra_args` in a native `long` and saves it in
return frames as `Val_long`. The arms need every reachable count, current or
saved in a frame, to be a small nonnegative integer. `ExtraBounded P` names
that premise; a concrete program discharges it by one checked run
(`OCaml/Programs/WhileMinExtra.lean`). The general invariant
(`extra ≤ stack length`, the extra arguments living on the stack) is open
(a2-sem).
-/

namespace OCaml.Bytecode

/-- Every return frame `.code r :: env :: .int ex :: _` in the stack saves a
nonnegative count. -/
def framesOk : List Val → Bool
  | .code _ :: env :: .int ex :: rest => decide (0 ≤ ex.toInt) && framesOk (env :: .int ex :: rest)
  | _ :: rest => framesOk rest
  | [] => true

theorem framesOk_tail (v : Val) (stk : List Val) (ok : framesOk (v :: stk) = true) :
    framesOk stk = true := by
  cases v with
  | code pc =>
    match stk, ok with
    | [], _ => rfl
    | [x], _ => cases x <;> rfl
    | env :: x :: rest, ok =>
      cases x with
      | int ex =>
        simp only [framesOk, Bool.and_eq_true] at ok
        exact ok.2
      | ptr | code | atom | raw => simpa only [framesOk] using ok
  | int | ptr | atom | raw => simpa only [framesOk] using ok

theorem framesOk_drop : ∀ (n : Nat) (stk : List Val), framesOk stk = true →
    ∀ {r : Nat} {env : Val} {ex : BitVec 63} {rest : List Val},
      stk.drop n = .code r :: env :: .int ex :: rest → 0 ≤ ex.toInt
  | 0, stk, ok, r, env, ex, rest, h => by
    simp only [List.drop_zero] at h
    subst h
    simp only [framesOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    exact ok.1
  | n + 1, [], _, _, _, _, _, h => by simp at h
  | n + 1, v :: stk, ok, _, _, _, _, h => by
    simp only [List.drop_succ_cons] at h
    exact framesOk_drop n stk (framesOk_tail v stk ok) h

/-- The per-state check. -/
def St.extraOk (s : St) : Bool := decide (s.extra < 2 ^ 62) && framesOk s.stack

/-- **Extra-argument counts are small and saved counts nonnegative.** -/
structure ExtraBounded (P : Prog) : Prop where
  small : ∀ s, Reach P s → s.extra < 2 ^ 62
  saved : ∀ s n r env ex rest, Reach P s →
    s.stack.drop n = .code r :: env :: .int ex :: rest → 0 ≤ ex.toInt

theorem ExtraBounded.of_check {P : Prog} (h : ∀ s, Reach P s → s.extraOk = true) :
    ExtraBounded P where
  small s reach := by
    have := h s reach
    simp only [St.extraOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  saved s n _ _ _ _ reach drop := by
    have := h s reach
    simp only [St.extraOk, Bool.and_eq_true] at this
    exact framesOk_drop n s.stack this.2 drop

end OCaml.Bytecode
