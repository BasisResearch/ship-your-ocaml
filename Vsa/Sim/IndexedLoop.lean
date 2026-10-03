import Vsa.Sim.DeriveLoop

namespace Vsa.Sim
open Vsa.Machine Vsa.Logic

/-- Fold an indexed machine invariant with a bounded, observed counter.
The invariant may include arbitrary context beyond the scanned payload. -/
theorem indexedLoop {I : Nat → Config → Prop} {index : Config → Nat} {start count : Nat}
    (observed : ∀ i c, I i c → index c = i)
    (bounded : ∀ i c, I i c → i ≤ count)
    (step : ∀ i, Triple (fun c => I i c ∧ i < count) (I (i + 1))) :
    Triple (I start) (I count) := by
  let Inv := fun c => I (index c) c
  let B := fun c => index c < count
  have body : ∀ n, Triple (fun c => Inv c ∧ B c ∧ count - index c = n)
      (fun c => Inv c ∧ count - index c < n) := by
    intro n c ⟨h, lt, rank⟩
    obtain ⟨d, run, post⟩ := step (index c) c ⟨h, lt⟩
    have next := observed _ _ post
    refine ⟨d, run, ?_, ?_⟩
    · change I (index d) d
      rw [next]; exact post
    · rw [next]; dsimp [B] at lt; omega
  apply (loopFromBody (fun c => count - index c) body).conseq
  · intro c h
    change I (index c) c
    rw [observed _ _ h]; exact h
  · intro c ⟨h, stop⟩
    have bound := bounded _ _ h
    have same : index c = count := by dsimp [B] at stop; omega
    simpa only [Inv, same] using h

end Vsa.Sim
