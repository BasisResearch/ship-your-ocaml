import OCaml.Run.Machine
import Vsa.Sim.BlockAdapter
import Vsa.Sim.DeriveCase

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps StepsN)
open Vsa.Logic (Triple TripleN)

namespace OCaml.Run

/-- A counter advanced by every successful kernel step records the run length. -/
theorem iter_counter {C O : Type} {f : C → Except O C} (count : C → Nat)
    (hs : ∀ {a b}, f a = .ok b → count b = count a + 1)
    {n : Nat} {a b : C} (h : iter f n a = .ok b) : count b = count a + n := by
  induction n generalizing a with
  | zero => cases h; omega
  | succ n ih =>
    change f a >>= _ = _ at h
    cases hf : f a with
    | error o => rw [hf] at h; cases h
    | ok c =>
      rw [hf] at h
      have hc := hs hf
      have hb := ih h
      omega

end OCaml.Run

namespace Vsa.Machine

theorem Step.steps_succ {a b : Config} (h : Step a b) : b.steps = a.steps + 1 := by
  cases h with
  | @mk σ σ' i i' u u' e =>

    show u' = u + 1

    unfold stepOnce at e
    repeat' first
      |
        (simp only [EStateM.Result.ok.injEq, Sum.inr.injEq, Prod.mk.injEq,
           reduceCtorEq, false_and] at e
         omega)
      |
        simp only [EStateM.Result.ok.injEq, reduceCtorEq, false_and] at e
      |
        simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
          Bind.bind, Pure.pure] at e
      |
        split at e

theorem Steps.steps_le {a b : Config} (hs : Steps a b) : a.steps ≤ b.steps := by
  obtain ⟨n, hn⟩ := OCaml.Run.vsa_steps_iff.1 hs
  have hc := OCaml.Run.iter_counter Config.steps
    (fun h => (OCaml.Run.vsaK_graph.iff.2 h).steps_succ) hn
  omega

theorem Steps.toN_of_stepsField {a b : Config} (hs : Steps a b) :
    StepsN (b.steps - a.steps) a b := by
  obtain ⟨n, hn⟩ := OCaml.Run.vsa_steps_iff.1 hs
  have hc := OCaml.Run.iter_counter Config.steps
    (fun h => (OCaml.Run.vsaK_graph.iff.2 h).steps_succ) hn
  have he : b.steps - a.steps = n := by omega
  rw [he]
  exact OCaml.Run.vsa_stepsN_iff.2 hn

theorem Steps.toN_of_stepsEq {a b : Config} {k : Nat}
    (hs : Steps a b) (hk : b.steps = a.steps + k) : StepsN k a b := by
  have := hs.toN_of_stepsField
  rw [hk] at this
  simpa using this

end Vsa.Machine

namespace Vsa.Sim

open Vsa.Machine

def LandedN (n : Nat) (c : Config) (P : Config → Prop) : Prop :=
  ∃ (m : Nat) (c' : Config), n ≤ m ∧ StepsN m c c' ∧ P c'

end Vsa.Sim
