import Vsa.Sim.DeriveLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic

/-- Fold a native loop whose observed cursor advances one bounded index per
iteration. The run construction is the existing well-founded loop rule. -/
theorem indexed_loop (index : Config → Nat) (count start : Nat) (At : Nat → Config → Prop)
    (bound : ∀ k c, At k c → k ≤ count)
    (observed : ∀ k c, At k c → index c = k)
    (next : ∀ k c, At k c → k < count → ∃ d, Steps c d ∧ At (k + 1) d) :
    Triple (At start) (At count) := by
  let I := fun c => At (index c) c
  let B := fun c => index c < count
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ count - index c = n)
      (fun c => I c ∧ count - index c < n) := by
    intro n c ⟨h, hk, hn⟩
    obtain ⟨d, run, post⟩ := next (index c) c h hk
    have idx := observed _ d post
    refine ⟨d, run, ?_, ?_⟩
    · change At (index d) d
      rw [idx]
      exact post
    · rw [idx]
      dsimp [B] at hk
      omega
  apply (loopFromBody (fun c => count - index c) body).conseq
  · intro c h
    change At (index c) c
    rw [observed start c h]
    exact h
  · intro c ⟨h, stop⟩
    have upper := bound (index c) c h
    have eq : index c = count := by dsimp [B] at stop; omega
    simpa only [I, eq] using h
end OCaml.Vm.Boot.Startup
