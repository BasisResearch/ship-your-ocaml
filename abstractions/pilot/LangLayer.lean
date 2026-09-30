import Pilot2
import Vsa.Lang.SmallStep
import Vsa.Lang.Densify

/-!
# LangLayer: Layer A plumbing through ship-your-interpreter's `Vsa/Lang`

Bake-off entrant `LangLayer` (round 1b). `Vsa/Lang/{Basic,Runs,SmallStep,Densify}`
are copied verbatim from ship-your-interpreter (`exponentiate`, 3274bd70).
The bridge presents `BcSem` as a `Vsa.Lang.SmallStep` (`bcSS`, `Next := Step`,
the graph of `bcK`), so `bcSS`'s runs enter the run kernel through
`bcK_graph` and `stepsN_iff`; the side condition is `Good P ∧ Fits B P`.
-/

namespace OCaml.Pilot2.LangLayer

open OCaml OCaml.Bytecode OCaml.Vm Vsa.Machine

/-! ## Section 1: the bridge (SETUP) -/

/-- `BcSem` as a `Vsa.Lang` small-step semantics. -/
abbrev bcSS : Vsa.Lang.SmallStep where
  Prog := Prog
  State := St
  init P := P.init
  Next := Step
  Final P s e out := ∃ w, step P s = .halt e w ∧ bytesToString w.console = out

/-- `bcSS`'s runs enter the run kernel by their cons presentation. -/
theorem ss_pres (P : Prog) : Run.ConsPres (Step P) (bcSS.StepsN P) where
  nil c := @Vsa.Lang.SmallStep.StepsN.zero bcSS P c
  cons s r := .succ s r
  inv := fun
    | .zero _ => .inl ⟨rfl, rfl⟩
    | .succ s r => .inr ⟨_, _, rfl, s, r⟩

theorem ss_stepsN_iff {P : Prog} {n : Nat} {a b : St} : bcSS.StepsN P n a b ↔ StepsN P n a b :=
  ((ss_pres P).iff (bcK_graph P)).trans stepsN_iff.symm

theorem ss_reach_iff {P : Prog} {s : St} : bcSS.Reach P s ↔ Reach P s :=
  exists_congr fun _ => ss_stepsN_iff

theorem ss_halts_iff {P : Prog} {e : Nat} {out : String} : bcSS.Halts P e out ↔ BcHalts P out e :=
  ⟨fun ⟨s, hr, w, hs, ho⟩ => ⟨s, w, ss_reach_iff.1 hr, hs, ho⟩,
   fun ⟨s, w, hr, hs, ho⟩ => ⟨s, ss_reach_iff.2 hr, w, hs, ho⟩⟩

theorem ss_diverges_iff {P : Prog} : bcSS.Diverges P ↔ BcDiverges P :=
  forall_congr' fun _ => exists_congr fun _ => ss_stepsN_iff

/-- The layer's side condition: fragment and budget. -/
def BcFits (B : Budget) (P : Prog) : Prop := Good P ∧ Fits B P

theorem progress {B : Budget} {P : Prog} (h : BcFits B P) : bcSS.Progress P := fun s hr => by
  obtain ⟨hu, hw⟩ := h.1 s (ss_reach_iff.1 hr)
  cases hst : step P s with
  | next s' => exact .inl ⟨s', ⟨hst⟩⟩
  | halt e w => exact .inr ⟨e, _, w, hst, rfl⟩
  | unsupported => exact (hu hst).elim
  | wrong => exact (hw hst).elim

/-- `BcSem` under the budget `B` as a (total) `Vsa.Lang.Lang`. -/
abbrev bcLang (B : Budget) : Vsa.Lang.Lang := bcSS.toLang (BcFits B) fun _ => progress

/-- `ArmSim`'s entry/next/halt sites are the layer's. -/
theorem armSim {L : Layout} {B : Budget} {P : Prog} (A : ArmSim L B P) :
    bcSS.ArmSim (BcFits B) (Loaded L) VmRepr P where
  entry c hL h := A.entry c hL h.1 h.2
  next s s' c hr h hv := fun ⟨e⟩ => A.next s s' c (ss_reach_iff.1 hr) h.1 h.2 hv e
  halt s e out c hr h hv := fun ⟨w, hs, ho⟩ => ho ▸ A.halt s e w c (ss_reach_iff.1 hr) h.1 h.2 hv hs

theorem simTotal_of_sim {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    (bcLang B).SimTotal (Loaded L) where
  term P c e out hL h hs := H.term_sim P c hL h.1 h.2 out e (ss_halts_iff.1 hs)
  div P c hL h hd := H.div_sim P c hL h.1 h.2 (ss_diverges_iff.1 hd)

theorem sim_of_simTotal {L : Layout} {B : Budget} (H : (bcLang B).SimTotal (Loaded L)) :
    OcamlrunSim L B where
  term_sim P c hL hg hf out e hb := H.term P c e out hL ⟨hg, hf⟩ (ss_halts_iff.2 hb)
  div_sim P c hL hg hf hd := H.div P c hL ⟨hg, hf⟩ (ss_diverges_iff.2 hd)

/-- The layer's conclusion, read back as `OcamlrunRefinement`'s body. -/
theorem refinement_of_refines {B : Budget} {P : Prog} {c : Config}
    (R : (bcLang B).RefinesTotal P c) :
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c) :=
  ⟨fun out e => ss_halts_iff.symm.trans (R.halts e out trivial), ss_diverges_iff.symm.trans R.diverges⟩

/-- Layer A through the layer: `ArmSim.simTotal` then `SimTotal.refinement`. -/
theorem layerA {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) {P : Prog} {c : Config}
    (hL : Loaded L P c) (hg : Good P) (hf : Fits B P) : (bcLang B).RefinesTotal P c :=
  (Vsa.Lang.SmallStep.ArmSim.simTotal fun P => armSim (A P)).refinement hL ⟨hg, hf⟩

/-- `bcModel` halts exactly as `bcSS` does (lockstep transport, run kernel). -/
theorem bcModel_halts_iff {P : Prog} {e : Nat} {out : String} :
    VsaIris.Halts (Logic.bcModel P) P.init e out ↔ bcSS.Halts P e out := by
  refine ⟨fun h => ss_halts_iff.2 (Logic.halts_bcHalts h), fun h => ?_⟩
  obtain ⟨w, hk, rfl⟩ := bcHalts_iff.1 (ss_halts_iff.1 h)
  obtain ⟨n, hn⟩ := Run.haltsK_iff.1 hk
  exact Run.mm_halts_iff.2 (Run.haltsK_iff.2
    ⟨n, (Run.iter_transport id Logic.gBc (Logic.bcModel_square P) n P.init).trans (by rw [hn]; rfl)⟩)

/-! ## Section 2: the held-out cases -/

theorem h10 : OCaml.Pilot2.H10 := fun _ _ A _ _ hL hg hf e =>
  exists_congr fun out => ss_halts_iff.symm.trans ((layerA A hL hg hf).halts e out trivial)

theorem h11 : OCaml.Pilot2.H11 := fun _ _ A _ _ hL hg hf out e =>
  bcModel_halts_iff.trans ((layerA A hL hg hf).halts e out trivial)

/-! ## Section 3: refactor R4 (statements identical to `OCaml/Refinement.lean`) -/

theorem ocamlrun_refinement_of_sim_r {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    OcamlrunRefinement L B := fun _ _ hL hg hf =>
  refinement_of_refines ((simTotal_of_sim H).refinement hL ⟨hg, hf⟩)

theorem ocamlrun_refinement_fillZero_r {L : Layout} {B : Budget} (H : OcamlrunSim L B) :
    ∀ P c, Loaded L P (Vsa.Densify.fillZero c) → Good P → Fits B P →
      (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c) := fun _ _ hL hg hf =>
  refinement_of_refines ((simTotal_of_sim H).refinement hL ⟨hg, hf⟩).of_fillZero

theorem run_sim_r {L : Layout} {B : Budget} {P : Prog} (A : ArmSim L B P) (hg : Good P)
    (hf : Fits B P) :
    ∀ {k : Nat} {s s' : St} {c : Config}, Reach P s → StepsN P k s s' → VmRepr P s c →
      ∃ n c', k ≤ n ∧ StepsN n c c' ∧ VmRepr P s' c' := fun hr hs hv =>
  (armSim A).run ⟨hg, hf⟩ (ss_reach_iff.2 hr) (ss_stepsN_iff.2 hs) hv

theorem simOfArms_r {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) : OcamlrunSim L B :=
  sim_of_simTotal (Vsa.Lang.SmallStep.ArmSim.simTotal fun P => armSim (A P))

theorem ocamlrun_refinement_of_arms_r {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) :
    OcamlrunRefinement L B := fun _ _ hL hg hf =>
  refinement_of_refines (layerA A hL hg hf)


end OCaml.Pilot2.LangLayer
