import OCaml
import VsaIris.Adequacy

/-!
# Held-out pilot suite, round 1b: the Layer A refinement plumbing

Target: `OCaml/Refinement.lean`'s simulation plumbing (`ocamlrun_refinement_of_sim`,
`ocamlrun_refinement_fillZero`, `run_sim`, `simOfArms`,
`ocamlrun_refinement_of_arms`: 55 proof lines), against ship-your-interpreter's
language-parametric layer `Vsa/Lang` (branch `exponentiate`). Nothing here is
proved; entrants prove H10, H11 and re-prove the five theorems with identical
statements (refactor R4).
-/

namespace OCaml.Pilot2

open OCaml.Bytecode OCaml.Vm Vsa.Machine

/-- H10: Layer A observing only the exit code. -/
def H10 : Prop :=
  ∀ (L : Layout) (B : Budget), (∀ P, ArmSim L B P) →
    ∀ P c, Loaded L P c → Good P → Fits B P →
      ∀ e, (∃ out, BcHalts P out e) ↔ (∃ out, Halts c out e)

/-- H11: Layer A against the Iris machine model of the bytecode (`bcModel`). -/
def H11 : Prop :=
  ∀ (L : Layout) (B : Budget), (∀ P, ArmSim L B P) →
    ∀ P c, Loaded L P c → Good P → Fits B P →
      ∀ out e, VsaIris.Halts (OCaml.Logic.bcModel P) P.init e out ↔ Halts c out e

end OCaml.Pilot2
