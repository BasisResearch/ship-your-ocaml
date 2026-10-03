import Vsa.Sim.DeriveLoop

namespace OCaml.Run
set_option autoImplicit false
open Vsa.Machine Vsa.Logic Vsa.Sim

/-- Lift a bounded natural-index invariant through concrete iterations. The
state-derived index makes the existing well-founded loop rule applicable;
clients supply machine execution only for one iteration. -/
theorem counted_loop (count : Nat) (index : Config → Nat) (I : Nat → Config → Prop)
    (indexed : ∀ i c, I i c → index c = i)
    (bounded : ∀ i c, I i c → i ≤ count)
    (body : ∀ i, Triple (fun c => I i c ∧ i < count) (I (i + 1))) :
    Triple (I 0) (I count) := by
  let invariant := fun c => I (index c) c
  let active := fun c => index c < count
  have iteration : ∀ n, Triple (fun c => invariant c ∧ active c ∧ count - index c = n)
      (fun c => invariant c ∧ count - index c < n) := by
    intro n c ⟨h, more, rank⟩
    obtain ⟨d, steps, post⟩ := body (index c) c ⟨h, more⟩
    have next := indexed _ _ post
    refine ⟨d, steps, ?_, ?_⟩
    · change I (index d) d
      rw [next]; exact post
    · rw [next]; dsimp [active] at more; omega
  apply (loopFromBody (fun c => count - index c) iteration).conseq
  · intro c h
    change I (index c) c
    rw [indexed _ _ h]; exact h
  · intro c ⟨h, stop⟩
    have bound := bounded _ _ h
    have final : index c = count := by dsimp [active] at stop; omega
    simpa only [invariant, final] using h

end OCaml.Run
