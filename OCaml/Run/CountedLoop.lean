import Vsa.Sim.DeriveLoop
import OCaml.Run.Machine

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

/-- Select a generated continuing or final machine branch and fold its native run. -/
theorem counted_loop_native (count : Nat) (index : Config → Nat) (I : Nat → Config → Prop)
    (indexed : ∀ i c, I i c → index c = i) (bounded : ∀ i c, I i c → i ≤ count)
    (more : ∀ i c, I i c → i < count → i + 1 < count →
      ∃ nb after, StepsN nb c after ∧ I (i + 1) after)
    (last : ∀ i c, I i c → i < count → i + 1 = count →
      ∃ nb after, StepsN nb c after ∧ I (i + 1) after) : Triple (I 0) (I count) := by
  apply counted_loop count index I indexed bounded
  intro i c ⟨h, bound⟩
  have body : ∃ nb after, StepsN nb c after ∧ I (i + 1) after := by
    by_cases next : i + 1 < count
    · exact more i c h bound next
    · exact last i c h bound (by omega)
  obtain ⟨nb, after, steps, post⟩ := body
  exact ⟨after, vsa_steps_iff.mpr ⟨nb, vsa_stepsN_iff.mp steps⟩, post⟩

end OCaml.Run
