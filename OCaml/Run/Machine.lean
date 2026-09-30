import OCaml.Run.Kernel
import Vsa.Machine

/-!
# The RISC-V machine as a run kernel

`vsaK` presents `Vsa.Machine.Step` as a kernel step function
(`OCaml/Run/Kernel.lean`). `Vsa.Machine.StepsN` and `Vsa.Machine.Steps`
enter by their presentations, and the machine's run laws are kernel
corollaries (discipline rule O5).
-/

namespace OCaml.Run

open Vsa.Machine

/-- The machine as a kernel; outcome `some (e, σ)` is an HTIF exit, `none`
anything else (Sail error, exit without code). -/
def vsaK (c : Config) : Except (Option (Nat × MState)) Config :=
  match (Vsa.stepOnce c.tick c.steps).run c.σ with
  | .ok (.inr (i', u')) σ' => .ok ⟨σ', i', u'⟩
  | .ok (.inl (some e, _)) σ' => .error (some (e, σ'))
  | _ => .error none

theorem vsaK_graph : Graph vsaK Step :=
  ⟨fun {a _} => ⟨fun ⟨h⟩ => by simp [vsaK, h], fun h => by
    obtain ⟨σ, i, u⟩ := a; unfold vsaK at h; split at h <;> (try cases h) <;> exact .mk ‹_›⟩⟩

theorem vsaK_halted {c : Config} {e : Nat} {σ : MState} :
    Halted c e σ ↔ vsaK c = .error (some (e, σ)) :=
  ⟨fun ⟨h⟩ => by simp [vsaK, h], fun h => by
    obtain ⟨σ, i, u⟩ := c; unfold vsaK at h; split at h <;> (try cases h) <;> exact .mk ‹_›⟩

theorem vsaStepsN_pres : ConsPres Step StepsN :=
  ⟨.zero, .succ, fun h => by cases h with | zero => exact .inl ⟨rfl, rfl⟩ | succ s r => exact .inr ⟨_, _, rfl, s, r⟩⟩

theorem vsaSteps_pres : ClosPres Step Steps :=
  -- discipline: allow(O5-run-induction) the ClosPres presentation's induction principle
  ⟨.refl, .head, fun _ h0 h1 _ _ h => by induction h with
    | refl => exact h0 _
    | head s r ih => exact h1 s r ih⟩

theorem vsa_stepsN_iff {n : Nat} {a b : Config} : StepsN n a b ↔ iter vsaK n a = .ok b :=
  vsaStepsN_pres.iff vsaK_graph

theorem vsa_steps_iff {a b : Config} : Steps a b ↔ Reach vsaK a b :=
  vsaSteps_pres.iff vsaK_graph

theorem vsa_diverges_iff {c : Config} : Diverges c ↔ DivK vsaK c :=
  forall_congr' fun _ => exists_congr fun _ => vsa_stepsN_iff

theorem vsa_halts_iff {c : Config} {out : String} {e : Nat} :
    Halts c out e ↔ ∃ σ, HaltsK vsaK c (some (e, σ)) ∧ output σ = out :=
  ⟨fun ⟨c', σ, hs, hh, ho⟩ => ⟨σ, ⟨c', vsa_steps_iff.1 hs, vsaK_halted.1 hh⟩, ho⟩,
   fun ⟨σ, ⟨c', hr, hh⟩, ho⟩ => ⟨c', σ, vsa_steps_iff.2 hr, vsaK_halted.2 hh, ho⟩⟩

end OCaml.Run
