import OCaml.Run.Kernel

/-! Local agreement of deterministic systems, lifted through the run kernel. -/
namespace OCaml.Run

/-- Two kernels have the same bounded run when they agree at each continuing
state visited before the bound. No condition is imposed on the final state. -/
theorem iter_eq_of_agree {C O : Type} (f g : C → Except O C) (n : Nat) (s : C)
    (agree : ∀ k, k < n → ∀ t, iter f k s = .ok t → f t = g t) :
    iter f n s = iter g n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have prev := ih (fun k hk => agree k (by omega))
    rw [iter_succ', iter_succ', ← prev]
    cases h : iter f n s with
    | error o => rfl
    | ok t => exact agree n (by omega) t h

/-- A partial simulation suffices for successful finite runs. In particular,
a local decoder may reject addresses outside its window. -/
theorem iter_ok_of_step {C O : Type} (f g : C → Except O C)
    (square : ∀ s t, f s = .ok t → g s = .ok t)
    (n : Nat) (s t : C) (h : iter f n s = .ok t) : iter g n s = .ok t := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    simp only [iter] at h ⊢
    cases hs : f s with
    | error o => rw [hs] at h; cases h
    | ok u =>
      rw [square s u hs]
      rw [hs] at h
      exact ih u h

end OCaml.Run
