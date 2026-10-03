import Vsa.Machine
namespace Vsa.Sim.Boot
/-- Compose successful item parsers by one abstract list proof. -/
theorem mapM_ok {ε α β : Type} (f : α → Except ε β) (g : α → β) (xs : List α)
    (items : ∀ a ∈ xs, f a = .ok (g a)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have head := items a (by simp)
    have tail := ih (fun b hb => items b (by simp [hb]))
    simp only [List.mapM_cons, List.map_cons, head, tail]
    rfl
end Vsa.Sim.Boot
