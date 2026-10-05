import OCaml.EndToEnd
import OCaml.RefinementF1
import OCaml.Logic.BcModel

/-!
# The headline statements, by name

Each is a `Prop` (never an axiom or `sorry`); PHASES.md is the ledger of who
proves what, when. What IS proved about them is listed after the
statements.
-/

namespace OCaml

open OCaml.Bytecode

/-- **Layer A.** The bare-metal `ocamlrun` refines `BcSem`
(`OCaml/Refinement.lean`: `OcamlrunRefinement`). -/
def ocamlrun_refinement_Statement (L : Layout) (B : Budget) : Prop := OcamlrunRefinement L B

/-- **Layer A for F1** (the current target, `OCaml/RefinementF1.lean`): the
same conclusion for programs that stay in F1 (`GoodF1`). Implied by
`ocamlrun_refinement_Statement` (`OcamlrunRefinement.f1`). -/
def ocamlrun_refinement_F1_Statement (L : Layout) (B : Budget) : Prop := OcamlrunRefinementF1 L B

/-- Open GC-safety obligation for the pinned compiler, for each loaded input
inside the supported fragment. The static scan and small-heap differential
runs are validation evidence, not inhabitants of this proposition. -/
def boot_ocamlc_gcSafe_Statement (load : Loader) (boot : List UInt8) : Prop :=
  ∀ argv fs P, load boot argv fs = some P → Good P → GcSafe P

/-- **Layer B′.** Adequacy of the machine-level program logic over `BcSem`
(`OCaml/Logic/BcModel.lean`). PROVED: `bytecode_logic_adequacy`. -/
def bytecode_logic_adequacy_Statement : Prop := Logic.BytecodeLogicAdequacy

theorem bytecode_logic_adequacy : bytecode_logic_adequacy_Statement := Logic.bytecodeLogicAdequacy

/-- **Layer C.** The back half of `ocamlc` is correct at the source level
(`OCaml/EndToEnd.lean`: `BackendCorrect`). -/
def ocamlc_backend_correct_Statement (S : SourceSem) (ocamlc : S.Program)
    (parse : List UInt8 → Option S.Program) (load : Loader) : Prop :=
  BackendCorrect S ocamlc parse load

/-- **The bootstrap fixpoint.** Under the source semantics, the compiler
compiles its own sources to exactly the bytes of `boot/ocamlc`
(`SelfCompiles`). -/
def boot_ocamlc_fixpoint_Statement (S : SourceSem) (ocamlc : S.Program) (bs : Bootstrap)
    (boot : List UInt8) : Prop :=
  SelfCompiles S ocamlc bs boot

/-- **End to end** (`EndToEnd`). -/
def endToEnd_ocaml_Statement (S : SourceSem) (parse : List UInt8 → Option S.Program)
    (load : Loader) (boot : List UInt8) (L : Layout) (B : Budget) : Prop :=
  EndToEnd S parse load boot L B

/-- **The composition is proved**: Layer A, Layer C (for user programs and
for the compiler's own build) and the fixpoint give the end-to-end
statement (`endToEnd_ocaml`). -/
theorem endToEnd_of_layers {S : SourceSem} {ocamlc : S.Program}
    {parse : List UInt8 → Option S.Program} {load : Loader} {bs : Bootstrap}
    {boot : List UInt8} {L : Layout} {B : Budget}
    (hA : ocamlrun_refinement_Statement L B)
    (hC : ocamlc_backend_correct_Statement S ocamlc parse load)
    (hCself : BackendCorrectFor S ocamlc load bs.argv bs.sources bs.output ocamlc)
    (hF : boot_ocamlc_fixpoint_Statement S ocamlc bs boot) :
    endToEnd_ocaml_Statement S parse load boot L B :=
  endToEnd_ocaml hA hC hCself hF

/-- **Layer A from its per-arm obligations is proved** (`simOfArms`). -/
theorem ocamlrun_refinement_of_arms' {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) :
    ocamlrun_refinement_Statement L B :=
  ocamlrun_refinement_of_arms A

/-- **Layer A for F1 from the per-opcode arm tables is proved**
(`F1Arms.simR`). -/
theorem ocamlrun_refinement_F1_of_arms {L : Layout} {B : Budget}
    (A : ∀ P c, Loaded L P c → GoodF1 P → Fits B P → GcSafe P → ∃ R, F1Arms P c R) :
    ocamlrun_refinement_F1_Statement L B :=
  ocamlrun_refinementF1_of_arms A

/-- Layer A observing only the exit code. -/
theorem ocamlrun_refinement_exit {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) {P : Prog} {c : Vsa.Machine.Config}
    (hL : Loaded L P c) (hg : Good P) (hf : Fits B P) (hgc : GcSafe P) (e : Nat) :
    (∃ out, BcHalts P out e) ↔ (∃ out, Vsa.Machine.Halts c out e) :=
  exists_congr fun out => (ocamlrun_refinement_of_arms A P c hL hg hf hgc).1 out e

/-- Layer A against the Iris machine model of the bytecode. -/
theorem ocamlrun_refinement_bcModel {L : Layout} {B : Budget} (A : ∀ P, ArmSim L B P) {P : Prog}
    {c : Vsa.Machine.Config} (hL : Loaded L P c) (hg : Good P) (hf : Fits B P) (hgc : GcSafe P) (out : String) (e : Nat) :
    VsaIris.Halts (Logic.bcModel P) P.init e out ↔ Vsa.Machine.Halts c out e :=
  Logic.halts_iff_bcHalts.trans ((ocamlrun_refinement_of_arms A P c hL hg hf hgc).1 out e)

end OCaml
