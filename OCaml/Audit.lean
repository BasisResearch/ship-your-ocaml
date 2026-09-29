import OCaml
import Vsa.Sim.MemcpySpec
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivLoops

/-! Axiom audit of every proved theorem of the scaffold (`scripts/check_all.sh`
stage a3 checks the output: only `propext`, `Classical.choice`,
`Quot.sound`). -/

#print axioms OCaml.Bytecode.halts_or_diverges
#print axioms OCaml.Bytecode.BcHalts.det
#print axioms OCaml.Bytecode.BcHalts.not_diverges
#print axioms OCaml.Bytecode.bcHalts_of_runTo
#print axioms OCaml.Bytecode.ledger_exact
#print axioms OCaml.Bytecode.ledger_fragment
#print axioms OCaml.Bytecode.f1_count
#print axioms OCaml.Bytecode.primF1_unsupported
#print axioms OCaml.ocamlrun_refinement_of_sim
#print axioms OCaml.ocamlrun_refinement_fillZero
#print axioms OCaml.simOfArms
#print axioms OCaml.ocamlrun_refinement_of_arms
#print axioms OCaml.Logic.bytecode_adequacy
#print axioms OCaml.Logic.bytecodeLogicAdequacy
#print axioms OCaml.boot_meaning
#print axioms OCaml.endToEnd_ocaml
#print axioms OCaml.Programs.whileMin_bcSem
#print axioms OCaml.bytecode_logic_adequacy
#print axioms OCaml.endToEnd_of_layers
#print axioms OCaml.ocamlrun_refinement_of_arms'

/-! Library proofs from ship-your-interpreter, retargeted to this ELF
(`scripts/retarget_syi.py`; pins checked by `scripts/check_code_pins.py`). -/
#print axioms Vsa.Sim.memcpy_bytepath_spec
#print axioms Vsa.Sim.muldi3_spec
#print axioms Vsa.Sim.udivdi3_spec
