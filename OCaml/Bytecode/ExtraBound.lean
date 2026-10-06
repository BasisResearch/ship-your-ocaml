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

/-- `p` holds at every suffix of a list (every possible frame position). -/
def suffixesOk (p : List Val → Bool) : List Val → Bool
  | [] => p []
  | v :: rest => p (v :: rest) && suffixesOk p rest

theorem suffixesOk_drop {p : List Val → Bool} :
    ∀ (n : Nat) (stk : List Val), suffixesOk p stk = true → p (stk.drop n) = true
  | 0, [], ok => ok
  | 0, _ :: _, ok => by simp only [suffixesOk, Bool.and_eq_true] at ok; exact ok.1
  | _ + 1, [], ok => ok
  | n + 1, _ :: stk, ok => by
    simp only [suffixesOk, Bool.and_eq_true] at ok
    exact suffixesOk_drop n stk ok.2

/-- A return frame `.code r :: env :: .int ex :: _` saves a nonnegative count. -/
def returnFrameOk : List Val → Bool
  | .code _ :: _ :: .int ex :: _ => decide (0 ≤ ex.toInt)
  | _ => true

/-- A trap frame `.code h :: .int link :: env :: .int ex :: _` saves a
nonnegative count. -/
def trapFrameOk : List Val → Bool
  | .code _ :: .int _ :: _ :: .int ex :: _ => decide (0 ≤ ex.toInt)
  | _ => true

/-- The per-state check. -/
def St.extraOk (s : St) : Bool :=
  decide (s.extra < 2 ^ 62) && suffixesOk returnFrameOk s.stack && suffixesOk trapFrameOk s.stack

/-- **Extra-argument counts are small and saved counts nonnegative.** -/
structure ExtraBounded (P : Prog) : Prop where
  small : ∀ s, Reach P s → s.extra < 2 ^ 62
  saved : ∀ s n r env ex rest, Reach P s →
    s.stack.drop n = .code r :: env :: .int ex :: rest → 0 ≤ ex.toInt
  /-- the same for trap frames (`raiseTo` restores `extra` from them) -/
  trapSaved : ∀ s n h link env ex rest, Reach P s →
    s.stack.drop n = .code h :: .int link :: env :: .int ex :: rest → 0 ≤ ex.toInt

theorem ExtraBounded.of_check {P : Prog} (h : ∀ s, Reach P s → s.extraOk = true) :
    ExtraBounded P where
  small s reach := by
    have := h s reach
    simp only [St.extraOk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1
  saved s n _ _ _ _ reach drop := by
    have := h s reach
    simp only [St.extraOk, Bool.and_eq_true] at this
    have frame := suffixesOk_drop n s.stack this.1.2
    rw [drop] at frame
    simpa [returnFrameOk] using frame
  trapSaved s n _ _ _ _ _ reach drop := by
    have := h s reach
    simp only [St.extraOk, Bool.and_eq_true] at this
    have frame := suffixesOk_drop n s.stack this.2
    rw [drop] at frame
    simpa [trapFrameOk] using frame

end OCaml.Bytecode
