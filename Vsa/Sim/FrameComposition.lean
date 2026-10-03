import Vsa.Sim.FrameOn

namespace Vsa.Sim

theorem outW_append (xs ys : List W) (a : Nat) :
    OutW (xs ++ ys) a ↔ OutW xs a ∧ OutW ys a := by
  induction xs with
  | nil => simp [OutW]
  | cons w xs ih => simp only [List.cons_append, OutW, ih, and_assoc]

/-- Sequential memory frames permit writes in the union of both finite
window lists. Each stage retains its own stronger frame for other uses. -/
theorem frameOn_comp {xs ys m0 m1 m2}
    (first : FrameOn xs m0 m1) (second : FrameOn ys m1 m2) :
    FrameOn (xs ++ ys) m0 m2 := by
  intro a outside
  obtain ⟨left,right⟩ := (outW_append xs ys a).mp outside
  exact (second a right).trans (first a left)

end Vsa.Sim
