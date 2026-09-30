import Vsa.Sim.StrcmpSites
import Vsa.Sim.SsprintSites
import Vsa.Sim.SsputsSites
import Vsa.Sim.ElfDecode
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
#print axioms OCaml.Loaded.runtime
#print axioms OCaml.Vm.not_promotedRuntimeOk_of_projection
#print axioms OCaml.Vm.Boot.WhileMinObservation.bounds
#print axioms OCaml.Vm.Boot.WhileMinObservation.noPending
#print axioms OCaml.Vm.Boot.WhileMinObservation.nursery_not_empty
#print axioms OCaml.Vm.Boot.WhileMinObservation.not_promoted
#print axioms OCaml.Vm.Boot.WhileMinObservation.not_loaded
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

/-! Adopted abstractions, abstraction-discovery round 1 (`abstractions/ROUND-1.md`). -/
#print axioms OCaml.Run.iter_add
#print axioms OCaml.Run.HaltsK.unique
#print axioms OCaml.Run.halts_or_div
#print axioms OCaml.Run.div_iff_not_halts
#print axioms OCaml.Run.ConsPres.iff
#print axioms OCaml.Run.ClosPres.iff
#print axioms OCaml.Run.iter_transport
#print axioms OCaml.Run.mm_halts_unique
#print axioms OCaml.Run.mm_reaches_iff
#print axioms OCaml.Logic.reaches_stepsN
#print axioms OCaml.Logic.halts_bcHalts
#print axioms Vsa.Machine.Halts.of_steps
#print axioms OCaml.Vm.Reloc.valWord_relocates
#print axioms OCaml.Vm.Reloc.objAt_reloc
#print axioms OCaml.Vm.Reloc.stackRepr_reloc
#print axioms OCaml.Vm.Reloc.heapRepr_reloc
#print axioms OCaml.Vm.Reloc.ScanCoherent.act
#print axioms OCaml.Bytecode.loop_rule
#print axioms OCaml.Bytecode.step_br_taken
#print axioms OCaml.Programs.CountLoop.loopN_reaches
#print axioms OCaml.Logic.halts_iff_bcHalts
#print axioms OCaml.ocamlrun_refinement_exit
#print axioms OCaml.ocamlrun_refinement_bcModel

/-! Library proofs from ship-your-interpreter, retargeted to this ELF
(`scripts/retarget_syi.py`; pins checked by `scripts/check_code_pins.py`). -/
#print axioms Vsa.Sim.memcpy_bytepath_spec
#print axioms Vsa.Sim.muldi3_spec
#print axioms Vsa.Sim.udivdi3_spec

/-! Symbolic allocation and closure capture (B′). -/
#print axioms OCaml.Bytecode.Heap.get_alloc_old
#print axioms OCaml.Bytecode.Heap.get_alloc_fresh
#print axioms OCaml.Bytecode.field_alloc_fresh
#print axioms OCaml.Bytecode.field_alloc_old
#print axioms OCaml.Bytecode.closure_capture_read
/-! A1: machine-checked obstruction to the current arm precondition. -/
#print axioms OCaml.Vm.Sim.repr_forceExit
#print axioms OCaml.Vm.Sim.forceExit_halted
#print axioms OCaml.Vm.Sim.forceExit_not_plus
#print axioms OCaml.Vm.Sim.armSim_not_repr
#print axioms OCaml.Vm.Sim.loaded_not_armSim

/-! Absolute-address code locality (B′). -/
#print axioms OCaml.Run.iter_eq_of_agree
#print axioms OCaml.Bytecode.decodeAt_local
#print axioms OCaml.Bytecode.code_extract_word
#print axioms OCaml.Bytecode.decodeAt_extract
#print axioms OCaml.Bytecode.CodeSlice.iter_eq
-- Generic Sail decode normal form and representative instruction families.
#print axioms Vsa.Sim.decodeN.eq
#print axioms Vsa.Sim.decodeW
#print axioms Vsa.Sim.ElfDecode.decode_0000006f
#print axioms Vsa.Sim.ElfDecode.decode_00000293

-- Retargeted StrcmpSites machine-step specifications.
#print axioms Vsa.Sim.site_80042b20
#print axioms Vsa.Sim.site_80042b24
#print axioms Vsa.Sim.site_80042b28
#print axioms Vsa.Sim.site_80006eac_taken
#print axioms Vsa.Sim.site_80006eac_nottaken
#print axioms Vsa.Sim.site_80042b30
#print axioms Vsa.Sim.site_80042b34
#print axioms Vsa.Sim.site_80042b38
#print axioms Vsa.Sim.site_80042b3c
#print axioms Vsa.Sim.site_80042b40
#print axioms Vsa.Sim.site_80042b44
#print axioms Vsa.Sim.site_80042b48
#print axioms Vsa.Sim.site_80042b4c
#print axioms Vsa.Sim.site_80006ed0_taken
#print axioms Vsa.Sim.site_80006ed0_nottaken
#print axioms Vsa.Sim.site_80006ed4_taken
#print axioms Vsa.Sim.site_80006ed4_nottaken
#print axioms Vsa.Sim.site_80042b58
#print axioms Vsa.Sim.site_80042b5c
#print axioms Vsa.Sim.site_80042b60
#print axioms Vsa.Sim.site_80042b64
#print axioms Vsa.Sim.site_80042b68
#print axioms Vsa.Sim.site_80042b6c
#print axioms Vsa.Sim.site_80006ef0_taken
#print axioms Vsa.Sim.site_80006ef0_nottaken
#print axioms Vsa.Sim.site_80006ef4_taken
#print axioms Vsa.Sim.site_80006ef4_nottaken
#print axioms Vsa.Sim.site_80042b78
#print axioms Vsa.Sim.site_80042b7c
#print axioms Vsa.Sim.site_80042b80
#print axioms Vsa.Sim.site_80042b84
#print axioms Vsa.Sim.site_80042b88
#print axioms Vsa.Sim.site_80042b8c
#print axioms Vsa.Sim.site_80006f10_taken
#print axioms Vsa.Sim.site_80006f10_nottaken
#print axioms Vsa.Sim.site_80042b94
#print axioms Vsa.Sim.site_80042b98
#print axioms Vsa.Sim.site_80006f1c_taken
#print axioms Vsa.Sim.site_80006f1c_nottaken
#print axioms Vsa.Sim.site_80042ba0
#print axioms Vsa.Sim.site_80042ba4
#print axioms Vsa.Sim.site_80006f28_taken
#print axioms Vsa.Sim.site_80006f28_nottaken
#print axioms Vsa.Sim.site_80042bac
#print axioms Vsa.Sim.site_80042bb0
#print axioms Vsa.Sim.site_80006f34_taken
#print axioms Vsa.Sim.site_80006f34_nottaken
#print axioms Vsa.Sim.site_80042bb8
#print axioms Vsa.Sim.site_80042bbc
#print axioms Vsa.Sim.site_80006f40_taken
#print axioms Vsa.Sim.site_80006f40_nottaken
#print axioms Vsa.Sim.site_80042bc4
#print axioms Vsa.Sim.site_80042bc8
#print axioms Vsa.Sim.site_80042bcc
#print axioms Vsa.Sim.site_80042bd0
#print axioms Vsa.Sim.site_80006f54_taken
#print axioms Vsa.Sim.site_80006f54_nottaken
#print axioms Vsa.Sim.site_80042bd8
#print axioms Vsa.Sim.site_80042bdc
#print axioms Vsa.Sim.site_80042be0
#print axioms Vsa.Sim.site_80042be4
#print axioms Vsa.Sim.site_80042be8
#print axioms Vsa.Sim.site_80006f6c_taken
#print axioms Vsa.Sim.site_80006f6c_nottaken
#print axioms Vsa.Sim.site_80042bf0
#print axioms Vsa.Sim.site_80042bf4
#print axioms Vsa.Sim.site_80042bf8
#print axioms Vsa.Sim.site_80042bfc
#print axioms Vsa.Sim.site_80042c00
#print axioms Vsa.Sim.site_80042c04
#print axioms Vsa.Sim.site_80042c08
#print axioms Vsa.Sim.site_80042c0c
#print axioms Vsa.Sim.site_80042c10
#print axioms Vsa.Sim.site_80006f94_taken
#print axioms Vsa.Sim.site_80006f94_nottaken
#print axioms Vsa.Sim.site_80006f98_taken
#print axioms Vsa.Sim.site_80006f98_nottaken
#print axioms Vsa.Sim.site_80042c1c
#print axioms Vsa.Sim.site_80042c20
#print axioms Vsa.Sim.site_80042c24
#print axioms Vsa.Sim.site_80042c28
#print axioms Vsa.Sim.site_80006fac_taken
#print axioms Vsa.Sim.site_80006fac_nottaken
#print axioms Vsa.Sim.site_80042c30
#print axioms Vsa.Sim.site_80042c34
#print axioms Vsa.Sim.site_80042c38
#print axioms Vsa.Sim.site_80042c3c
#print axioms Vsa.Sim.site_80006fc0_taken
#print axioms Vsa.Sim.site_80006fc0_nottaken
#print axioms Vsa.Sim.site_80042c44
#print axioms Vsa.Sim.site_80042c48

-- Retargeted SsprintSites machine-step specifications.
#print axioms Vsa.Sim.site_8000e908_sr
#print axioms Vsa.Sim.site_8000e90c_sr
#print axioms Vsa.Sim.site_8000e910_sr
#print axioms Vsa.Sim.site_8000e914_sr
#print axioms Vsa.Sim.site_8000e918_sr
#print axioms Vsa.Sim.site_8000e91c_nottaken_sr
#print axioms Vsa.Sim.site_8000e920_sr
#print axioms Vsa.Sim.site_8000e924_sr
#print axioms Vsa.Sim.site_8000e928_sr
#print axioms Vsa.Sim.site_8000e92c_sr
#print axioms Vsa.Sim.site_8000e930_sr
#print axioms Vsa.Sim.site_8000e934_sr
#print axioms Vsa.Sim.site_8000e938_sr
#print axioms Vsa.Sim.site_8000e93c_sr
#print axioms Vsa.Sim.site_8000e940_sr
#print axioms Vsa.Sim.site_8000e944_sr
#print axioms Vsa.Sim.site_8000e950_sr
#print axioms Vsa.Sim.site_8000e954_sr
#print axioms Vsa.Sim.site_8000e958_sr
#print axioms Vsa.Sim.site_8000e95c_sr
#print axioms Vsa.Sim.site_8000e960_nottaken_sr
#print axioms Vsa.Sim.site_8000e964_sr
#print axioms Vsa.Sim.site_8000e968_nottaken_sr
#print axioms Vsa.Sim.site_8000e96c_sr
#print axioms Vsa.Sim.site_8000e970_sr
#print axioms Vsa.Sim.site_8000e974_sr
#print axioms Vsa.Sim.site_8000e978_sr
#print axioms Vsa.Sim.site_8000e97c_sr
#print axioms Vsa.Sim.site_8000e980_nottaken_sr
#print axioms Vsa.Sim.site_8000e984_sr
#print axioms Vsa.Sim.site_8000e988_sr
#print axioms Vsa.Sim.site_8000e990_sr
#print axioms Vsa.Sim.site_8000e994_sr
#print axioms Vsa.Sim.site_8000e998_taken_sr_tgt
#print axioms Vsa.Sim.site_8000e998_taken_sr
#print axioms Vsa.Sim.site_8000e998_nottaken_sr
#print axioms Vsa.Sim.site_8000e99c_sr
#print axioms Vsa.Sim.site_8000e9a0_sr
#print axioms Vsa.Sim.site_8000e9a4_sr
#print axioms Vsa.Sim.site_8000e9a8_sr
#print axioms Vsa.Sim.site_8000e9ac_sr
#print axioms Vsa.Sim.site_8000e9b0_sr
#print axioms Vsa.Sim.site_8000e9b4_sr
#print axioms Vsa.Sim.site_8000e9b8_sr
#print axioms Vsa.Sim.site_8000e9bc_sr
#print axioms Vsa.Sim.site_8000e9c0_sr
#print axioms Vsa.Sim.site_8000e9c4_sr
#print axioms Vsa.Sim.site_8000e9c8_sr

-- Retargeted SsputsSites machine-step specifications.
#print axioms Vsa.Sim.site_1438c_sp
#print axioms Vsa.Sim.site_14390_sp
#print axioms Vsa.Sim.site_14394_sp
#print axioms Vsa.Sim.site_14398_sp
#print axioms Vsa.Sim.site_1439c_sp
#print axioms Vsa.Sim.site_143a0_sp
#print axioms Vsa.Sim.site_143a4_sp
#print axioms Vsa.Sim.site_143a8_sp
#print axioms Vsa.Sim.site_143ac_sp
#print axioms Vsa.Sim.site_143b0_sp
#print axioms Vsa.Sim.site_143b4_sp
#print axioms Vsa.Sim.site_143b8_sp
#print axioms Vsa.Sim.site_143bc_sp
#print axioms Vsa.Sim.site_143c0_sp
#print axioms Vsa.Sim.site_143c4_sp
#print axioms Vsa.Sim.site_143c8_sp
#print axioms Vsa.Sim.site_143cc_sp
#print axioms Vsa.Sim.site_143d0_sp
#print axioms Vsa.Sim.site_143d4_sp
#print axioms Vsa.Sim.site_143d8_sp
#print axioms Vsa.Sim.site_143dc_sp
#print axioms Vsa.Sim.site_143e0_sp
#print axioms Vsa.Sim.site_143e4_sp
#print axioms Vsa.Sim.site_143e8_sp
#print axioms Vsa.Sim.site_143ec_sp
#print axioms Vsa.Sim.site_143f0_sp
