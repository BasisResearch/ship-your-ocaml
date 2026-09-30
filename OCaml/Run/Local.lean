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

end OCaml.Run
