import Pilot2

/-!
# Pilot 1b, incumbent entrant

Only what the repository already has: `OCaml/Refinement.lean`'s vocabulary
(`ocamlrun_refinement_of_arms`), the run kernel (`OCaml/Run/*`) and
`OCaml/Logic/BcModel.lean`'s lockstep square.
-/

namespace OCaml.Pilot2.Incumbent1b

open OCaml.Bytecode OCaml.Vm Vsa.Machine OCaml.Logic

/-! ## Setup -/

/-- The converse of `halts_bcHalts`: a `BcSem` halt is a `bcModel` halt,
through the same lockstep square. -/
theorem bcHalts_halts {P : Prog} {e : Nat} {out : String} (h : BcHalts P out e) :
    VsaIris.Halts (bcModel P) P.init e out := by
  obtain ⟨w, hh, ho⟩ := bcHalts_iff.1 h
  obtain ⟨n, hn⟩ := Run.haltsK_iff.1 hh
  subst ho
  refine Run.mm_halts_iff.2 (Run.haltsK_iff.2 ⟨n, ?_⟩)
  exact (Run.iter_transport id gBc (bcModel_square P) n P.init).trans (by rw [hn]; rfl)

/-- `bcModel` halts exactly as `BcSem` does. -/
theorem halts_iff_bcHalts {P : Prog} {e : Nat} {out : String} :
    VsaIris.Halts (bcModel P) P.init e out ↔ BcHalts P out e :=
  ⟨halts_bcHalts, bcHalts_halts⟩

/-! ## Held-out cases -/

theorem h10 : OCaml.Pilot2.H10 := fun _ _ A P c hL hg hf e =>
  exists_congr fun out => (ocamlrun_refinement_of_arms A P c hL hg hf).1 out e

theorem h11 : OCaml.Pilot2.H11 := fun _ _ A P c hL hg hf out e =>
  halts_iff_bcHalts.trans ((ocamlrun_refinement_of_arms A P c hL hg hf).1 out e)

/-! ## R4 shortening experiments

The incumbent's R4 numbers are the proofs in `OCaml/Refinement.lean` as they
stand. These are the three that the repository's own tools shorten; the
statements are copied verbatim. -/

theorem ocamlrun_refinement_of_sim_r {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    OcamlrunRefinement L B := by
  intro P c hL hg hf
  have fwd := H.term_sim P c hL hg hf
  have dv := H.div_sim P c hL hg hf
  rcases halts_or_diverges P hg with ⟨out', e', hb⟩ | hbd
  · refine ⟨fun out e => ⟨fwd out e, fun hm => ?_⟩, dv, fun hd => (Diverges.not_halts hd (fwd out' e' hb)).elim⟩
    obtain ⟨rfl, rfl⟩ := hm.deterministic (fwd out' e' hb); exact hb
  · exact ⟨fun out e => ⟨fwd out e, fun hm => (Diverges.not_halts (dv hbd) hm).elim⟩, dv, fun _ => hbd⟩

theorem run_sim_r {L : Layout} {B : Budget} {P : Prog} (A : ArmSim L B P) (hg : Good P)
    (hf : Fits B P) :
    ∀ {k : Nat} {s s' : St} {c : Config}, Reach P s → StepsN P k s s' → VmRepr P s c →
      ∃ n c', k ≤ n ∧ StepsN n c c' ∧ VmRepr P s' c' := by
  intro k s s' c hr hs hv
  -- discipline: allow(O5-run-induction) run_sim is the simulation induction (one ArmSim per BcSem step), not run algebra
  induction hs generalizing c with
  | zero => exact ⟨0, c, Nat.le_refl _, .zero _, hv⟩
  | @succ k a b d st _ ih =>
    obtain ⟨e⟩ := st
    obtain ⟨c1, ⟨n1, h1⟩, hv1⟩ := A.next a b c hr hg hf hv e
    obtain ⟨hn, hk⟩ := hr
    obtain ⟨n2, c2, hle, h2, hv2⟩ := ih ⟨hn + 1, hk.snoc (.mk e)⟩ hv1
    exact ⟨n1 + 1 + n2, c2, by omega, h1.append h2, hv2⟩

theorem simOfArms_r {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) : OcamlrunSim L B where
  term_sim := by
    intro P c hL hg hf out e ⟨s, w, ⟨k, hk⟩, hst, ho⟩
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A P).entry c hL hg hf
    obtain ⟨n, c', -, hn, hv⟩ := run_sim (A P) hg hf ⟨0, .zero _⟩ hk hv0
    exact Halts.of_steps (h0.toSteps.trans' hn.toSteps) (ho ▸ (A P).halt s e w c' ⟨k, hk⟩ hg hf hv hst)
  div_sim := by
    intro P c hL hg hf hd m
    obtain ⟨c0, ⟨n0, h0⟩, hv0⟩ := (A P).entry c hL hg hf
    obtain ⟨s, hs⟩ := hd m
    obtain ⟨n, c', hle, hn, -⟩ := run_sim (A P) hg hf ⟨0, .zero _⟩ hs hv0
    obtain ⟨d, hd'⟩ := Nat.exists_eq_add_of_le (show m ≤ n0 + 1 + n by omega)
    exact Vsa.Machine.StepsN.prefix' (hd' ▸ h0.append hn)

end OCaml.Pilot2.Incumbent1b
