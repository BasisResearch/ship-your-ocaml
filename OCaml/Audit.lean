import OCaml.Vm.Gc.FirstYoungAccess
import OCaml.Vm.Gc.FirstForwarded
import OCaml.Vm.Boot.Startup.MallocBootAlign
import OCaml.Vm.Gc.RelocatedPayload
import OCaml.Vm.Gc.ForwardedInitial
import OCaml.Vm.Gc.ForwardedLoop
import OCaml.Vm.Boot.Startup.MallocBootPrefix
import OCaml.Vm.Gc.ForwardedContext
import OCaml.Vm.Gc.ForwardedObservations
import OCaml.Vm.Gc.ForwardedIteration
import OCaml.Vm.Gc.ForwardedScan
import OCaml.Vm.Gc.ForwardedField
import OCaml.Vm.Boot.Startup.AllocatorInitial
import OCaml.Vm.Boot.Startup.SbrkBootstrap
import OCaml.Vm.Gc.ForwardedAdvance
import OCaml.Vm.Boot.Startup.WhileMinToMalloc
import OCaml.Vm.Gc.MopupResume
import OCaml.Vm.Gc.ForwardedCall
import OCaml.Vm.Boot.Startup.AllocatorBootstrap
import OCaml.Vm.Boot.Startup.CamlMainPrefix
import OCaml.Vm.Boot.Startup.DomainPrefix
import OCaml.Vm.Boot.Startup.CamlMainCalls
import OCaml.Vm.Boot.Startup.DomainCalls
import OCaml.Vm.Gc.OldifySaved
import OCaml.Vm.Boot.Startup.StatAlloc
import OCaml.Vm.Boot.Startup.StatAllocCalls
import OCaml.Vm.Boot.Startup.BssReads
import OCaml.Vm.Gc.EnqueueReturn
import OCaml.Vm.Boot.WhileMinElfLoaded
import OCaml.Vm.Gc.ForwardedReturn
import OCaml.Vm.Gc.ForwardedAccess
import OCaml.Vm.Boot.WhileMinElfMetadata
import OCaml.Os.HtifMemory
import OCaml.Os.DirectoryObstruction
import OCaml.Bytecode.Callback
import OCaml.Vm.Primitives.StringCopyReadback
import OCaml.Programs.LazyForce
import OCaml.Vm.Gc.Observed
import OCaml.Vm.Primitives.StringCopyFast
import OCaml.Vm.GcObservation
import OCaml.Vm.Primitives.StringConstructorLayout
import OCaml.Vm.Primitives.StringAllocationLayout
import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Boot.Startup.ToCamlMain
import OCaml.Vm.Boot.Startup.Reset
import OCaml.Vm.Boot.Startup.InitializeRegisters
import OCaml.Vm.Boot.Startup.PrimitiveLookupRows
import OCaml.Vm.Boot.Startup.PrimitiveLookupCalls
import OCaml.Vm.Boot.Startup.CompareNames
import OCaml.Vm.Primitives.LibraryMemcpy
import OCaml.Vm.Primitives.StringReadback
import OCaml.Vm.Primitives.SmallAllocation
import OCaml.Vm.Primitives.StringFast
import OCaml.Vm.Primitives.LibraryStrlen
import OCaml.Vm.Boot.WhileMin
import OCaml.Vm.Boot.WhileMinEntry
import OCaml.Vm.Boot.WhileMinRuntime
import OCaml.Vm.Boot.Heap
import OCaml.Vm.Boot.FreeList
import OCaml.Vm.Boot.WhileMinLogChecks
import Vsa.Sim.Boot.Bytes
import OCaml.Vm.Gc.Generated.Audit
import OCaml.Vm.Gc.QueueAccess
import OCaml.Vm.Gc.QueueEnqueue
import OCaml.Vm.Gc.PendingPayload
import OCaml.Vm.Gc.QueueEmpty
import OCaml.Vm.Gc.MixedPayload
import Vsa.Sim.DeriveCaseRow
import VsaIris.Vsa.SnpFmt
import VsaIris.Vsa.SnpPrint
import VsaIris.Vsa.SnpStrlen
import VsaIris.Vsa.SnpArith
import VsaIris.Vsa.LibraryFormat
import VsaIris.Vsa.SegRun
import VsaIris.Vsa.FreeRunAll
import VsaIris.Vsa.MallocRunAll
import VsaIris.Vsa.MallocExtend
import VsaIris.Vsa.HeapFree
import VsaIris.Vsa.HeapCarve
import VsaIris.Vsa.HeapMoveAt
import VsaIris.Vsa.HeapClear
import VsaIris.Vsa.AllocSteps
import Vsa.Sim.SnprintfSpec20
import Vsa.Sim.StrcmpSpecCond
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


#print axioms OCaml.Os.htif_addresses_distinct
#print axioms OCaml.Os.longName_eof_rejected
#print axioms OCaml.Os.longName_not_special
#print axioms OCaml.Os.htifEntries

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
#print axioms OCaml.Vm.RuntimeOk.youngPtr_bounds
#print axioms OCaml.Vm.mailbox_layout
#print axioms OCaml.Vm.Boot.WhileMinObservation.bounds
#print axioms OCaml.Vm.Boot.WhileMinObservation.noPending
#print axioms OCaml.Vm.Boot.WhileMinObservation.nursery_not_empty
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

-- Whole-function strcmp, both aligned and unaligned entry paths.
#print axioms Vsa.Sim.strcmp_full_spec_cond
#print axioms Vsa.Sim.strcmp_full_spec
#print axioms Vsa.Sim.strcmp_word_spec
#print axioms Vsa.Sim.strcmp_byte_path
/-! Strengthened A1 representation and placement-independent platform frame. -/
#print axioms OCaml.Loaded.platform
#print axioms OCaml.Vm.PlatformOk.htif_done
#print axioms OCaml.Vm.Sim.forceExit_not_running
#print axioms Vsa.Sim.tr_isint
#print axioms OCaml.Vm.Sim.isintWord_eq
#print axioms OCaml.Vm.Sim.ofBool_int
#print axioms OCaml.Vm.Sim.valWord_parity
#print axioms OCaml.Vm.Sim.isintWord_repr
#print axioms OCaml.Vm.Sim.isint_not_valWord
#print axioms OCaml.Vm.Sim.isint_arm
#print axioms OCaml.Vm.Sim.isint_loaded
#print axioms Vsa.Sim.tr_const0
#print axioms OCaml.Vm.Sim.const0_loaded
#print axioms Vsa.Sim.site_800035c0_const0
#print axioms Vsa.Sim.site_800035c4_const0
#print axioms Vsa.Sim.site_800035c8_const0
/-! Generated smoke sites for the 18 extended ALU classes. -/
#print axioms Vsa.Sim.site_800002c0_alu
#print axioms Vsa.Sim.site_80001e38_alu
#print axioms Vsa.Sim.site_80001efc_alu
#print axioms Vsa.Sim.site_80001f00_alu
#print axioms Vsa.Sim.site_80002294_alu
#print axioms Vsa.Sim.site_80002870_alu
#print axioms Vsa.Sim.site_80002874_alu
#print axioms Vsa.Sim.site_80002cdc_alu
#print axioms Vsa.Sim.site_8000314c_alu
#print axioms Vsa.Sim.site_800032e8_alu
#print axioms Vsa.Sim.site_800032ec_alu
#print axioms Vsa.Sim.site_80003374_alu
#print axioms Vsa.Sim.site_8000344c_alu
#print axioms Vsa.Sim.site_80003540_alu
#print axioms Vsa.Sim.site_800035a0_alu
#print axioms Vsa.Sim.site_800035b8_alu
#print axioms Vsa.Sim.site_80006234_alu
#print axioms Vsa.Sim.site_8000d8fc_alu
#print axioms OCaml.Vm.Reloc.platformOk_reloc
#print axioms OCaml.Vm.Reloc.loopRegisters_reloc

/-! Generated bytecode windows and summary composition (B′).
Every generated block rule is also audited by scripts/check_bc_audit.py. -/
#print axioms OCaml.Run.iter_ok_of_step
#print axioms OCaml.Bytecode.decoded_run_sound
#print axioms OCaml.Bytecode.CertifiedBlock.decode_sound
#print axioms OCaml.Bytecode.CertifiedBlock.run
#print axioms OCaml.Bytecode.call_summary
#print axioms OCaml.Bytecode.tail_summary
#print axioms OCaml.Bytecode.sym_instr
#print axioms OCaml.Bytecode.apply1_enter
#print axioms OCaml.Bytecode.return_over
#print axioms OCaml.Bytecode.grab_under
#print axioms OCaml.Bytecode.restart_partial
#print axioms OCaml.Logic.pc_alias_excluded
#print axioms OCaml.Logic.pc_eq_of_reg
#print axioms OCaml.Logic.reachesN_of_symbolic
#print axioms OCaml.Programs.Generated.Demo.jumpStop_summary
#print axioms OCaml.Programs.Generated.Demo.capture_summary
#print axioms OCaml.Programs.GeneratedAdequacy.jump_runFact
#print axioms OCaml.Programs.GeneratedAdequacy.jump_haltFact
#print axioms OCaml.Programs.GeneratedAdequacy.jump_wp
#print axioms OCaml.Programs.GeneratedAdequacy.jump_hyp
#print axioms OCaml.Programs.GeneratedAdequacy.jumpStop_adequacy

-- Short non-overlapping copies and the two-iovec stdio flush at this ELF.
#print axioms Vsa.Sim.memmove_fwd_spec
#print axioms Vsa.Sim.ssputs_fast_spec
#print axioms Vsa.Sim.ssprint_iov2_spec

-- Generic symbolic-run soundness and regenerated allocator instruction examples.
#print axioms OCaml.Run.iter_counter
#print axioms Vsa.Machine.Steps.toN_of_stepsField
#print axioms Vsa.Sim.segEval_sound
#print axioms VsaIris.Inst.seg_runFact
#print axioms VsaIris.Sym.swp_step
#print axioms VsaIris.Sym.swp_jal
#print axioms VsaIris.Sym.st_800375b8
#print axioms VsaIris.Sym.st_80044868

-- Allocator geometry and checked SWP paths at the OCaml ELF addresses.
#print axioms Vsa.Sim.DlHeap.bin_base_alignment
#print axioms Vsa.Sim.DlHeap.HeapAt.node_fields_ne
#print axioms Vsa.Sim.DlHeap.HeapAt.node_header_disjoint
#print axioms VsaIris.VsaHeap.PHeapAt.take
#print axioms VsaIris.VsaHeap.PHeapAt.carve
#print axioms VsaIris.VsaHeap.PHeapAt.splitFree
#print axioms VsaIris.VsaHeap.PHeapAt.moveBinAt
#print axioms VsaIris.VsaHeap.PHeapAt.release
#print axioms VsaIris.VsaHeap.PHeapAt.coalNext
#print axioms VsaIris.VsaHeap.PHeapAt.coalPrev
#print axioms VsaIris.VsaHeap.MHeap.bin_off_stack
#print axioms VsaIris.VsaHeap.sbrk_r_gen
#print axioms VsaIris.VsaHeap.sbrk_r_run
#print axioms VsaIris.VsaHeap.small_take
#print axioms VsaIris.VsaHeap.lr_take
#print axioms VsaIris.VsaHeap.top_split
#print axioms VsaIris.VsaHeap.ext_grow
#print axioms VsaIris.VsaHeap.extend_top

-- Complete allocator entry contracts at the current ELF addresses.
#print axioms VsaIris.Sym.read64_word_log
#print axioms VsaIris.VsaHeap.link_words_disjoint
#print axioms VsaIris.VsaHeap.bw_split_ret
#print axioms VsaIris.VsaHeap.malloc_all
#print axioms VsaIris.VsaHeap.mallocChgRun_proved
#print axioms VsaIris.VsaHeap.mallocLocalRun_proved

-- Free, coalescing and trimming at the current ELF addresses.
#print axioms Vsa.Sim.DlHeap.HeapAt.chunk_node_fields_ne
#print axioms Vsa.Sim.DlHeap.HeapAt.node_header_span_disjoint
#print axioms VsaIris.VsaHeap.trim_run
#print axioms VsaIris.VsaHeap.free_body
#print axioms VsaIris.VsaHeap.freeChgRun_proved
#print axioms VsaIris.VsaHeap.freeLocalRun_proved

-- Regenerated stdio SWP steps and formatter helper contracts.
#print axioms VsaIris.Sym.ntD_8003fe64
#print axioms VsaIris.Sym.nt_80042144
#print axioms VsaIris.Sym.memmove_nw
#print axioms VsaIris.Sym.strlen_nw
#print axioms VsaIris.Sym.ssputs_nw
#print axioms VsaIris.Interp.udiv_nw
#print axioms VsaIris.Interp.umod_nw
#print axioms Vsa.Sim.digits_eq_natToString
#print axioms VsaIris.Sym.ssprint_nw

-- Formatter entry, sign branches and return at the relocated code addresses.
#print axioms VsaIris.Interp.ldv_lw_store8
#print axioms VsaIris.Sym.svf_entry
#print axioms VsaIris.Sym.svf_printSign0
#print axioms VsaIris.Sym.svf_epi

-- Complete formatter conversion/loop and entry-to-return contracts.
#print axioms VsaIris.Sym.svf_convS
#print axioms VsaIris.Sym.svf_intQ
#print axioms VsaIris.Sym.svf_intD
#print axioms VsaIris.Sym.svf_digits
#print axioms VsaIris.Sym.loop_fmt
#print axioms VsaIris.Sym.svfprintf_nw

-- Complete conditional VM-data relocation (collector execution remains open).
#print axioms OCaml.Vm.Reloc.vmReprAt_reloc
#print axioms Vsa.Sim.tr_negint
#print axioms OCaml.Vm.Sim.negint_loaded

-- A6 safety interfaces, checked Forward obstructions, and candidate live budget.
#print axioms OCaml.Vm.Gc.forwardValue_int
#print axioms OCaml.Vm.Gc.forwardValue_not_isInt
#print axioms OCaml.Vm.Gc.scanCoherent_forward_int_obstruction
#print axioms OCaml.Vm.Gc.forward_objAt_obstruction
#print axioms OCaml.Vm.Gc.LoopHead.running
#print axioms OCaml.Vm.Gc.LoopHead.reloc
#print axioms OCaml.Vm.Gc.rememberedComplete_empty
#print axioms OCaml.Vm.Gc.liveWordsFrom_le
#print axioms OCaml.Vm.Gc.liveWords_le_allocated
#print axioms OCaml.Vm.Gc.fitsLive_of_fits
#print axioms Vsa.Sim.tr_acc0
#print axioms OCaml.Vm.Sim.accu_restore
#print axioms OCaml.Vm.Sim.accu_arm
#print axioms OCaml.Vm.Sim.RamReadAt.toNat
#print axioms OCaml.Vm.Sim.RamReadAt.window
#print axioms OCaml.Vm.Sim.field_selection
#print axioms OCaml.Vm.Sim.FieldSelection.sourceWord
#print axioms OCaml.Vm.Sim.FieldSelection.read
#print axioms OCaml.Vm.Sim.represented_register
#print axioms Vsa.Sim.tr_envacc1
#print axioms OCaml.Vm.Sim.envacc1_loaded
#print axioms OCaml.Vm.Sim.envacc1_arm
#print axioms Vsa.Sim.tr_envacc2
#print axioms OCaml.Vm.Sim.envacc2_loaded
#print axioms OCaml.Vm.Sim.envacc2_arm
#print axioms Vsa.Sim.tr_envacc3
#print axioms OCaml.Vm.Sim.envacc3_loaded
#print axioms OCaml.Vm.Sim.envacc3_arm
#print axioms Vsa.Sim.tr_envacc4
#print axioms OCaml.Vm.Sim.envacc4_loaded
#print axioms OCaml.Vm.Sim.envacc4_arm
#print axioms Vsa.Sim.tr_getfield0
#print axioms OCaml.Vm.Sim.getfield0_loaded
#print axioms OCaml.Vm.Sim.getfield0_arm
#print axioms Vsa.Sim.tr_getfield1
#print axioms OCaml.Vm.Sim.getfield1_loaded
#print axioms OCaml.Vm.Sim.getfield1_arm
#print axioms Vsa.Sim.tr_getfield2
#print axioms OCaml.Vm.Sim.getfield2_loaded
#print axioms OCaml.Vm.Sim.getfield2_arm
#print axioms Vsa.Sim.tr_getfield3
#print axioms OCaml.Vm.Sim.getfield3_loaded
#print axioms OCaml.Vm.Sim.getfield3_arm
#print axioms OCaml.Vm.Sim.stack_value_root
#print axioms OCaml.Vm.Sim.stack_slot_nat
#print axioms OCaml.Vm.Sim.acc0_arm
#print axioms OCaml.Vm.Sim.acc1_arm
#print axioms OCaml.Vm.Sim.acc2_arm
#print axioms OCaml.Vm.Sim.acc3_arm
#print axioms OCaml.Vm.Sim.acc4_arm
#print axioms OCaml.Vm.Sim.acc5_arm
#print axioms OCaml.Vm.Sim.acc6_arm
#print axioms OCaml.Vm.Sim.acc7_arm
#print axioms Vsa.Sim.tr_acc1
#print axioms OCaml.Vm.Sim.acc1_loaded
#print axioms Vsa.Sim.tr_acc2
#print axioms OCaml.Vm.Sim.acc2_loaded
#print axioms Vsa.Sim.tr_acc3
#print axioms OCaml.Vm.Sim.acc3_loaded
#print axioms Vsa.Sim.tr_acc4
#print axioms OCaml.Vm.Sim.acc4_loaded
#print axioms Vsa.Sim.tr_acc5
#print axioms OCaml.Vm.Sim.acc5_loaded
#print axioms Vsa.Sim.tr_acc6
#print axioms OCaml.Vm.Sim.acc6_loaded
#print axioms Vsa.Sim.tr_acc7
#print axioms OCaml.Vm.Sim.acc7_loaded
#print axioms OCaml.Vm.Sim.acc0_loaded

#print axioms Vsa.Sim.tr_acc
#print axioms OCaml.Vm.Sim.acc_loaded

-- Logical remembered-set rule; machine caml_modify summary remains open.
#print axioms OCaml.Vm.Gc.slotComplete_store
#print axioms OCaml.Vm.Gc.rememberedComplete_of_slots

-- Ported adapter consumed by whole-function generation.
#print axioms Vsa.Sim.segToTriple
-- F1 primitive constant family and representation/frame composition.
#print axioms OCaml.Vm.Primitives.block_summary
#print axioms OCaml.Vm.Primitives.leaf_of_blocks
#print axioms OCaml.Vm.Primitives.payload_of_repr
#print axioms OCaml.Vm.Primitives.VmPayload.frame
#print axioms OCaml.Vm.Primitives.VmPayload.accu_int
#print axioms OCaml.Vm.Primitives.constant_contract
#print axioms OCaml.Vm.Primitives.runtime_memory_stable
#print axioms OCaml.Vm.Primitives.caml_sys_const_naked_pointers_checked_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_big_endian_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_word_size_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_int_size_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_max_wosize_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_ostype_unix_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_ostype_win32_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_ostype_cygwin_primitive
#print axioms OCaml.Vm.Primitives.caml_sys_const_backend_type_primitive

-- Read-only primitive frames and signed tagged comparison.
#print axioms OCaml.Vm.Primitives.register_of_blocks
#print axioms OCaml.Vm.Primitives.immediate_contract
#print axioms OCaml.Vm.Primitives.tag_toNat
#print axioms OCaml.Vm.Primitives.tag_toInt
#print axioms OCaml.Vm.Primitives.tag_signed_lt
#print axioms OCaml.Vm.Primitives.compareWord_tag
#print axioms OCaml.Vm.Primitives.caml_int_compare_primitive
#print axioms Vsa.Sim.tr_dispatch
#print axioms OCaml.Vm.Sim.dispatch_loaded

#print axioms Vsa.Sim.PinsHold.get

-- Pinned dispatch-table entries and their checked indirect targets.
#print axioms OCaml.Vm.Sim.dispatchOffset_loaded
#print axioms OCaml.Vm.Sim.dispatchOffset_target
#print axioms OCaml.Vm.Sim.dispatchOpcode_guard
#print axioms OCaml.Vm.Sim.dispatchTarget_aligned
#print axioms OCaml.Vm.Sim.dispatchTarget_clear
-- Promotion may recolor a header without changing its representation.
#print axioms OCaml.Vm.Reloc.headerView_color

-- All generated collector/barrier segments, rows and code pins.
#audit_gc_rows

/-! A2 executable heap representation and measured compiler coverage. -/
#print axioms OCaml.Bytecode.Heap.storage_list_eq
#print axioms OCaml.Bytecode.Heap.storage_size_eq
#print axioms OCaml.Bytecode.Heap.get?_eq_getArray
#print axioms OCaml.Bytecode.executed_opcodes_ledgered
#print axioms OCaml.Bytecode.executed_primitives_ledgered

#print axioms OCaml.Bytecode.osCall_sound
#print axioms OCaml.Os.htifFsImplements_of_functions
#print axioms OCaml.Vm.Sim.dispatchIndex
#print axioms OCaml.Vm.Sim.dispatchIndex_nat
#print axioms OCaml.Vm.Sim.dispatchIndex_lower
#print axioms OCaml.Vm.Sim.dispatchIndex_upper
#print axioms OCaml.Vm.Sim.dispatchIndex_htif
#print axioms OCaml.Vm.Sim.dispatch_run

-- Represented CONST0 arm under explicit dispatch readiness.
#print axioms OCaml.Vm.Sim.payload_pc
#print axioms OCaml.Vm.Sim.ArmInput.running
#print axioms OCaml.Vm.Sim.ArmInput.of_repr
#print axioms OCaml.Vm.Sim.DispatchPost.image
#print axioms OCaml.Vm.Sim.immediate_arm
#print axioms Vsa.Sim.tr_const1
#print axioms OCaml.Vm.Sim.const1_loaded
#print axioms OCaml.Vm.Sim.const1_arm
#print axioms Vsa.Sim.tr_const2
#print axioms OCaml.Vm.Sim.const2_loaded
#print axioms OCaml.Vm.Sim.const2_arm
#print axioms Vsa.Sim.tr_const3
#print axioms OCaml.Vm.Sim.const3_loaded
#print axioms OCaml.Vm.Sim.const3_arm
#print axioms OCaml.Vm.Sim.const0_arm

-- Shared immediate-result restoration and modular NEGINT.
#print axioms OCaml.Vm.Sim.CodeReadAt.toNat
#print axioms OCaml.Vm.Sim.code_read
#print axioms OCaml.Vm.Sim.OperandAt.read
#print axioms OCaml.Vm.Sim.OperandAt.read32
#print axioms OCaml.Vm.Sim.target_int
#print axioms OCaml.Vm.Sim.relative_code_word

-- Immediate integer comparisons with both relative branch outcomes.
#print axioms OCaml.Vm.Sim.longVal_native
#print axioms OCaml.Vm.Sim.compare_code_word
#print axioms OCaml.Vm.Sim.brOp_accu
#print axioms Vsa.Sim.tr_bltint_jump
#print axioms OCaml.Vm.Sim.bltint_jump_loaded
#print axioms OCaml.Vm.Sim.bltint_jump_arm
#print axioms Vsa.Sim.tr_bltint_next
#print axioms OCaml.Vm.Sim.bltint_next_loaded
#print axioms OCaml.Vm.Sim.bltint_next_arm
#print axioms OCaml.Vm.Sim.bltint_step_arm
#print axioms Vsa.Sim.tr_bleint_jump
#print axioms OCaml.Vm.Sim.bleint_jump_loaded
#print axioms OCaml.Vm.Sim.bleint_jump_arm
#print axioms Vsa.Sim.tr_bleint_next
#print axioms OCaml.Vm.Sim.bleint_next_loaded
#print axioms OCaml.Vm.Sim.bleint_next_arm
#print axioms OCaml.Vm.Sim.bleint_step_arm
#print axioms Vsa.Sim.tr_bgtint_jump
#print axioms OCaml.Vm.Sim.bgtint_jump_loaded
#print axioms OCaml.Vm.Sim.bgtint_jump_arm
#print axioms Vsa.Sim.tr_bgtint_next
#print axioms OCaml.Vm.Sim.bgtint_next_loaded
#print axioms OCaml.Vm.Sim.bgtint_next_arm
#print axioms OCaml.Vm.Sim.bgtint_step_arm
#print axioms Vsa.Sim.tr_bgeint_jump
#print axioms OCaml.Vm.Sim.bgeint_jump_loaded
#print axioms OCaml.Vm.Sim.bgeint_jump_arm
#print axioms Vsa.Sim.tr_bgeint_next
#print axioms OCaml.Vm.Sim.bgeint_next_loaded
#print axioms OCaml.Vm.Sim.bgeint_next_arm
#print axioms OCaml.Vm.Sim.bgeint_step_arm
#print axioms Vsa.Sim.tr_bultint_jump
#print axioms OCaml.Vm.Sim.bultint_jump_loaded
#print axioms OCaml.Vm.Sim.bultint_jump_arm
#print axioms Vsa.Sim.tr_bultint_next
#print axioms OCaml.Vm.Sim.bultint_next_loaded
#print axioms OCaml.Vm.Sim.bultint_next_arm
#print axioms OCaml.Vm.Sim.bultint_step_arm
#print axioms Vsa.Sim.tr_bugeint_jump
#print axioms OCaml.Vm.Sim.bugeint_jump_loaded
#print axioms OCaml.Vm.Sim.bugeint_jump_arm
#print axioms Vsa.Sim.tr_bugeint_next
#print axioms OCaml.Vm.Sim.bugeint_next_loaded
#print axioms OCaml.Vm.Sim.bugeint_next_arm
#print axioms OCaml.Vm.Sim.bugeint_step_arm
#print axioms Vsa.Sim.tr_branch
#print axioms OCaml.Vm.Sim.branch_loaded
#print axioms OCaml.Vm.Sim.branch_arm

-- Shared control restoration and both guarded conditional paths.
#print axioms OCaml.Vm.Sim.control_arm

-- Runtime atom-table binding and the retained legacy word obstruction.
#print axioms OCaml.Vm.Boot.WhileMinHeap.read_atom_table
#print axioms OCaml.Vm.Sim.atom_word_of_binding
#print axioms OCaml.Vm.Sim.captured_atom_not_legacy
#print axioms OCaml.Vm.Sim.index_word
#print axioms OCaml.Vm.Sim.atom_index_offset
#print axioms OCaml.Vm.Sim.atom_negative_index_obstruction
#print axioms OCaml.Vm.Sim.atom0_loaded
#print axioms OCaml.Vm.Sim.atom_loaded
#print axioms OCaml.Vm.Sim.atom0_arm
#print axioms OCaml.Vm.Sim.atom_arm
#print axioms Vsa.Sim.tr_atom0
#print axioms Vsa.Sim.tr_atom

-- Indexed operand loads through the common generated template.
#print axioms OCaml.Vm.Sim.acc_arm
#print axioms OCaml.Vm.Sim.envacc_arm
#print axioms OCaml.Vm.Sim.getfield_arm
#print axioms OCaml.Vm.Sim.envacc_loaded
#print axioms OCaml.Vm.Sim.getfield_loaded
#print axioms Vsa.Sim.tr_envacc
#print axioms Vsa.Sim.tr_getfield

-- Shared read-only payload restoration and stack-consuming integer arms.
#print axioms OCaml.Vm.Sim.readOnly_restore
#print axioms OCaml.Vm.Sim.stack_drop
#print axioms OCaml.Vm.Sim.live_stack_drop
#print axioms OCaml.Vm.Sim.payload_stack_drop
-- Shared dispatch, payload assembly and represented stack-write restoration.
#print axioms OCaml.Vm.Sim.dispatch_compose
#print axioms OCaml.Vm.Sim.running_of_payload
#print axioms OCaml.Vm.Sim.live_stack_of_root
#print axioms OCaml.Vm.Sim.payload_stack_of_root
#print axioms OCaml.Vm.Sim.stack_push
#print axioms OCaml.Vm.Sim.payload_stack_push
#print axioms OCaml.Vm.Sim.live_stack_push
#print axioms OCaml.Vm.Sim.push_address
#print axioms OCaml.Vm.Sim.PushWriteOk.toNat
#print axioms OCaml.Vm.Sim.PushWriteOk.code
#print axioms OCaml.Vm.Sim.push_value_restore
#print axioms OCaml.Vm.Sim.push_value_arm
#print axioms OCaml.Vm.Sim.push_arm
#print axioms OCaml.Vm.Sim.pushacc0_arm
#print axioms OCaml.Vm.Sim.FieldSelection.read_payload
#print axioms OCaml.Vm.Sim.FieldSelection.word_frame
#print axioms OCaml.Vm.Sim.pushenvacc1_arm
#print axioms Vsa.Sim.pushenvacc1_code_store
#print axioms Vsa.Sim.tr_pushenvacc1
#print axioms OCaml.Vm.Sim.pushenvacc1_loaded
#print axioms OCaml.Vm.Sim.pushenvacc2_arm
#print axioms Vsa.Sim.pushenvacc2_code_store
#print axioms Vsa.Sim.tr_pushenvacc2
#print axioms OCaml.Vm.Sim.pushenvacc2_loaded
#print axioms OCaml.Vm.Sim.pushenvacc3_arm
#print axioms Vsa.Sim.pushenvacc3_code_store
#print axioms Vsa.Sim.tr_pushenvacc3
#print axioms OCaml.Vm.Sim.pushenvacc3_loaded
#print axioms OCaml.Vm.Sim.pushenvacc4_arm
#print axioms Vsa.Sim.pushenvacc4_code_store
#print axioms Vsa.Sim.tr_pushenvacc4
#print axioms OCaml.Vm.Sim.pushenvacc4_loaded
#print axioms OCaml.Vm.Sim.pushoffsetclosurem3_arm
#print axioms Vsa.Sim.pushoffsetclosurem3_code_store
#print axioms Vsa.Sim.tr_pushoffsetclosurem3
#print axioms OCaml.Vm.Sim.pushoffsetclosurem3_loaded
#print axioms OCaml.Vm.Sim.pushoffsetclosure0_arm
#print axioms Vsa.Sim.pushoffsetclosure0_code_store
#print axioms Vsa.Sim.tr_pushoffsetclosure0
#print axioms OCaml.Vm.Sim.pushoffsetclosure0_loaded
#print axioms OCaml.Vm.Sim.pushoffsetclosure3_arm
#print axioms Vsa.Sim.pushoffsetclosure3_code_store
#print axioms Vsa.Sim.tr_pushoffsetclosure3
#print axioms OCaml.Vm.Sim.pushoffsetclosure3_loaded

#print axioms OCaml.Vm.Sim.PushWriteOk.operand_read32
#print axioms OCaml.Vm.Sim.pushconstint_arm
#print axioms Vsa.Sim.pushconstint_code_store
#print axioms Vsa.Sim.tr_pushconstint
#print axioms OCaml.Vm.Sim.pushconstint_loaded
#print axioms OCaml.Vm.Sim.pushoffsetclosure_arm
#print axioms Vsa.Sim.pushoffsetclosure_code_store
#print axioms Vsa.Sim.tr_pushoffsetclosure
#print axioms OCaml.Vm.Sim.pushoffsetclosure_loaded

#print axioms OCaml.Vm.Sim.pushed_value
#print axioms OCaml.Vm.Sim.pushed_root
#print axioms OCaml.Vm.Sim.PushWriteOk.pushed_read
#print axioms OCaml.Vm.Sim.PushWriteOk.word_read
#print axioms OCaml.Vm.Sim.pushacc_arm
#print axioms Vsa.Sim.pushacc_code_store
#print axioms Vsa.Sim.tr_pushacc
#print axioms OCaml.Vm.Sim.pushacc_loaded
#print axioms OCaml.Vm.Sim.pushenvacc_arm
#print axioms Vsa.Sim.pushenvacc_code_store
#print axioms Vsa.Sim.tr_pushenvacc
#print axioms OCaml.Vm.Sim.pushenvacc_loaded
#print axioms OCaml.Vm.Sim.pushatom0_arm
#print axioms Vsa.Sim.pushatom0_code_store
#print axioms Vsa.Sim.tr_pushatom0
#print axioms OCaml.Vm.Sim.pushatom0_loaded
#print axioms OCaml.Vm.Sim.pushatom_arm
#print axioms Vsa.Sim.pushatom_code_store
#print axioms Vsa.Sim.tr_pushatom
#print axioms OCaml.Vm.Sim.pushatom_loaded

#print axioms OCaml.Vm.Sim.getglobal_arm
#print axioms Vsa.Sim.tr_getglobal
#print axioms OCaml.Vm.Sim.getglobal_loaded
#print axioms OCaml.Vm.Sim.pushgetglobal_arm
#print axioms Vsa.Sim.tr_pushgetglobal
#print axioms OCaml.Vm.Sim.pushgetglobal_loaded
#print axioms Vsa.Sim.pushgetglobal_code_store

#print axioms OCaml.Vm.Sim.FieldSelection.read_reachable
#print axioms OCaml.Vm.Sim.FieldSelection.word_frame_reachable
#print axioms OCaml.Vm.Sim.FieldSelection.load_frame
#print axioms OCaml.Vm.Sim.getglobalfield_arm
#print axioms Vsa.Sim.tr_getglobalfield
#print axioms OCaml.Vm.Sim.getglobalfield_loaded
#print axioms OCaml.Vm.Sim.pushgetglobalfield_arm
#print axioms Vsa.Sim.tr_pushgetglobalfield
#print axioms OCaml.Vm.Sim.pushgetglobalfield_loaded
#print axioms Vsa.Sim.pushgetglobalfield_code_store

#print axioms OCaml.Vm.Sim.beq_pointer_guard_obstruction
#print axioms OCaml.Vm.Sim.beq_pointer_falls_through
#print axioms OCaml.Vm.Sim.beq_step_arm
#print axioms OCaml.Vm.Sim.beq_jump_arm
#print axioms Vsa.Sim.tr_beq_jump
#print axioms OCaml.Vm.Sim.beq_jump_loaded
#print axioms OCaml.Vm.Sim.beq_next_arm
#print axioms Vsa.Sim.tr_beq_next
#print axioms OCaml.Vm.Sim.beq_next_loaded
#print axioms OCaml.Vm.Sim.bneq_step_arm
#print axioms OCaml.Vm.Sim.bneq_jump_arm
#print axioms Vsa.Sim.tr_bneq_jump
#print axioms OCaml.Vm.Sim.bneq_jump_loaded
#print axioms OCaml.Vm.Sim.bneq_next_arm
#print axioms Vsa.Sim.tr_bneq_next
#print axioms OCaml.Vm.Sim.bneq_next_loaded

#print axioms OCaml.Vm.Sim.WordEquality.guard
#print axioms OCaml.Vm.Sim.WordEquality.ints
#print axioms OCaml.Vm.Sim.eq_step_arm
#print axioms OCaml.Vm.Sim.eq_true_arm
#print axioms Vsa.Sim.tr_eq_true
#print axioms OCaml.Vm.Sim.eq_true_loaded
#print axioms OCaml.Vm.Sim.eq_false_arm
#print axioms Vsa.Sim.tr_eq_false
#print axioms OCaml.Vm.Sim.eq_false_loaded
#print axioms OCaml.Vm.Sim.neq_step_arm
#print axioms OCaml.Vm.Sim.neq_true_arm
#print axioms Vsa.Sim.tr_neq_true
#print axioms OCaml.Vm.Sim.neq_true_loaded
#print axioms OCaml.Vm.Sim.neq_false_arm
#print axioms Vsa.Sim.tr_neq_false
#print axioms OCaml.Vm.Sim.neq_false_loaded

#print axioms OCaml.Vm.Sim.SizeSelection.of_object
#print axioms OCaml.Vm.Sim.header_size_tag
#print axioms OCaml.Vm.Sim.vectlength_arm
#print axioms OCaml.Vm.Sim.vectlength_step_arm
#print axioms OCaml.Vm.Sim.vectlength_loaded
#print axioms Vsa.Sim.tr_vectlength

#print axioms OCaml.Vm.Sim.StackPost.registers
#print axioms OCaml.Vm.Sim.StackPost.loopRegisters
#print axioms OCaml.Vm.Sim.StackPost.after_dispatch
#print axioms OCaml.Vm.Sim.image_word_code
#print axioms OCaml.Vm.Sim.payload_frame_stack
#print axioms OCaml.Vm.Sim.stack_assign
#print axioms OCaml.Vm.Sim.assigned_root
#print axioms OCaml.Vm.Sim.payload_stack_assign
#print axioms OCaml.Vm.Sim.assign_restore
#print axioms OCaml.Vm.Sim.assign_body_arm
#print axioms OCaml.Vm.Sim.assign_arm
#print axioms OCaml.Vm.Sim.assign_step_arm
#print axioms OCaml.Vm.Sim.assign_loaded
#print axioms Vsa.Sim.assign_code_store
#print axioms Vsa.Sim.tr_assign
#print axioms OCaml.Vm.Sim.loopRegisters_frame
#print axioms OCaml.Vm.Sim.Ccall1Saved.frame
#print axioms OCaml.Vm.Sim.c_call1_primitive_return
#print axioms OCaml.Vm.Sim.c_call1_readOnly_summary
#print axioms OCaml.Vm.Sim.c_call1_return
#print axioms OCaml.Vm.Sim.ccall_primitive_return
#print axioms OCaml.Vm.Sim.ccall_readOnly_summary
#print axioms OCaml.Vm.Sim.ccall_return_sp
#print axioms OCaml.Vm.Sim.ccall_return_restore
#print axioms OCaml.Vm.Sim.ccall_primitive_result
#print axioms OCaml.Vm.Sim.ccall_result_restore
#print axioms OCaml.Vm.Sim.CcallnSaved.frame
#print axioms OCaml.Vm.Sim.ccalln_return_sp
#print axioms OCaml.Vm.Sim.c_calln_primitive_return
#print axioms OCaml.Vm.Sim.c_calln_readOnly_summary
#print axioms OCaml.Vm.Sim.c_calln_return
#print axioms OCaml.Vm.Sim.c_calln_return_triple
#print axioms OCaml.Vm.Sim.writeWindow_nat
#print axioms OCaml.Vm.Sim.CcallnWriteOk.stored
#print axioms OCaml.Vm.Sim.ccalln_log_in
#print axioms OCaml.Vm.Sim.ccalln_runtime
#print axioms OCaml.Vm.Sim.ccalln_array
#print axioms OCaml.Vm.Sim.ccalln_frame_address
#print axioms OCaml.Vm.Sim.ccalln_count_word
#print axioms OCaml.Vm.Sim.c_calln_setup
#print axioms OCaml.Vm.Sim.c_calln_arm
#print axioms OCaml.Vm.Sim.c_calln_step_arm
#print axioms OCaml.Vm.Sim.c_calln_callee_of_readOnly
#print axioms OCaml.Vm.Sim.c_call2_return
#print axioms OCaml.Vm.Sim.c_call2_return_triple
#print axioms OCaml.Vm.Sim.c_call3_return
#print axioms OCaml.Vm.Sim.c_call3_return_triple
#print axioms OCaml.Vm.Sim.c_call4_return
#print axioms OCaml.Vm.Sim.c_call4_return_triple
#print axioms OCaml.Vm.Sim.c_call5_return
#print axioms OCaml.Vm.Sim.c_call5_return_triple
#print axioms OCaml.Vm.Sim.c_call1_resume
#print axioms OCaml.Vm.Sim.c_call1_sys_argv
#print axioms Vsa.Sim.StepFrameOut.widenChecked
#print axioms OCaml.Vm.Sim.word_writeLog_at
#print axioms OCaml.Vm.Sim.word_read_writeLog_out
#print axioms OCaml.Vm.Sim.outLRange_sublist
#print axioms OCaml.Vm.Sim.Ccall1WriteOk.savedEnv
#print axioms OCaml.Vm.Sim.ccall1_savedStack
#print axioms OCaml.Vm.Sim.ccall1_runtime
#print axioms OCaml.Vm.Sim.c_call1_setup
#print axioms OCaml.Vm.Sim.ccall_argument_load
#print axioms OCaml.Vm.Sim.ccall_arguments_repr
#print axioms OCaml.Vm.Sim.c_call2_setup
#print axioms OCaml.Vm.Sim.c_call3_setup
#print axioms OCaml.Vm.Sim.c_call4_setup
#print axioms OCaml.Vm.Sim.c_call5_setup
#print axioms OCaml.Vm.Sim.c_call1_return_triple
#print axioms OCaml.Vm.Sim.c_call1_arm
#print axioms OCaml.Vm.Sim.ccall_callee_of_readOnly
#print axioms OCaml.Vm.Sim.c_call2_int_compare_callee
#print axioms OCaml.Vm.Sim.c_call2_arm
#print axioms OCaml.Vm.Sim.c_call2_step_arm
#print axioms OCaml.Vm.Sim.c_call3_arm
#print axioms OCaml.Vm.Sim.c_call3_step_arm
#print axioms OCaml.Vm.Sim.c_call4_arm
#print axioms OCaml.Vm.Sim.c_call4_step_arm
#print axioms OCaml.Vm.Sim.c_call5_arm
#print axioms OCaml.Vm.Sim.c_call5_step_arm
#print axioms OCaml.Vm.Sim.c_call1_step_arm
#print axioms OCaml.Vm.Sim.c_call1_callee_of_readOnly
#print axioms OCaml.Vm.Sim.c_call1_sys_argv_callee
#print axioms Vsa.Sim.tr_c_call2_prefix
#print axioms OCaml.Vm.Sim.c_call2_prefix_loaded
#print axioms Vsa.Sim.tr_c_call2_suffix
#print axioms OCaml.Vm.Sim.c_call2_suffix_loaded
#print axioms Vsa.Sim.tr_c_call3_prefix
#print axioms OCaml.Vm.Sim.c_call3_prefix_loaded
#print axioms Vsa.Sim.tr_c_call3_suffix
#print axioms OCaml.Vm.Sim.c_call3_suffix_loaded
#print axioms Vsa.Sim.tr_c_call4_prefix
#print axioms OCaml.Vm.Sim.c_call4_prefix_loaded
#print axioms Vsa.Sim.tr_c_call4_suffix
#print axioms OCaml.Vm.Sim.c_call4_suffix_loaded
#print axioms Vsa.Sim.tr_c_call5_prefix
#print axioms OCaml.Vm.Sim.c_call5_prefix_loaded
#print axioms Vsa.Sim.tr_c_call5_suffix
#print axioms Vsa.Sim.tr_c_calln_prefix
#print axioms OCaml.Vm.Sim.c_calln_prefix_loaded
#print axioms Vsa.Sim.tr_c_calln_suffix
#print axioms OCaml.Vm.Sim.c_calln_suffix_loaded
#print axioms OCaml.Vm.Sim.c_call5_suffix_loaded
#print axioms Vsa.Sim.StepFrameOut.of_jalr
#print axioms Vsa.Sim.pins_jalr
#print axioms Vsa.Sim.tr_c_call1_prefix
#print axioms Vsa.Sim.tr_c_call1_suffix
#print axioms OCaml.Vm.Sim.c_call1_prefix_loaded
#print axioms OCaml.Vm.Sim.c_call1_suffix_loaded
#print axioms OCaml.Vm.Sim.PushWriteOk.stack_read
#print axioms OCaml.Vm.Sim.pushacc1_arm
#print axioms OCaml.Vm.Sim.pushacc2_arm
#print axioms Vsa.Sim.pushacc2_code_store
#print axioms Vsa.Sim.tr_pushacc2
#print axioms OCaml.Vm.Sim.pushacc2_loaded
#print axioms OCaml.Vm.Sim.pushacc3_arm
#print axioms Vsa.Sim.pushacc3_code_store
#print axioms Vsa.Sim.tr_pushacc3
#print axioms OCaml.Vm.Sim.pushacc3_loaded
#print axioms OCaml.Vm.Sim.pushacc4_arm
#print axioms Vsa.Sim.pushacc4_code_store
#print axioms Vsa.Sim.tr_pushacc4
#print axioms OCaml.Vm.Sim.pushacc4_loaded
#print axioms OCaml.Vm.Sim.pushacc5_arm
#print axioms Vsa.Sim.pushacc5_code_store
#print axioms Vsa.Sim.tr_pushacc5
#print axioms OCaml.Vm.Sim.pushacc5_loaded
#print axioms OCaml.Vm.Sim.pushacc6_arm
#print axioms Vsa.Sim.pushacc6_code_store
#print axioms Vsa.Sim.tr_pushacc6
#print axioms OCaml.Vm.Sim.pushacc6_loaded
#print axioms OCaml.Vm.Sim.pushacc7_arm
#print axioms Vsa.Sim.pushacc7_code_store
#print axioms Vsa.Sim.tr_pushacc7
#print axioms OCaml.Vm.Sim.pushacc7_loaded
#print axioms OCaml.Vm.Sim.pushconst0_arm
#print axioms Vsa.Sim.pushconst0_code_store
#print axioms Vsa.Sim.tr_pushconst0
#print axioms OCaml.Vm.Sim.pushconst0_loaded
#print axioms OCaml.Vm.Sim.pushconst1_arm
#print axioms Vsa.Sim.pushconst1_code_store
#print axioms Vsa.Sim.tr_pushconst1
#print axioms OCaml.Vm.Sim.pushconst1_loaded
#print axioms OCaml.Vm.Sim.pushconst2_arm
#print axioms Vsa.Sim.pushconst2_code_store
#print axioms Vsa.Sim.tr_pushconst2
#print axioms OCaml.Vm.Sim.pushconst2_loaded
#print axioms OCaml.Vm.Sim.pushconst3_arm
#print axioms Vsa.Sim.pushconst3_code_store
#print axioms Vsa.Sim.tr_pushconst3
#print axioms OCaml.Vm.Sim.pushconst3_loaded

-- Exact memory effects for generated stack-write bodies.
#print axioms Vsa.Sim.push_code_store
#print axioms Vsa.Sim.tr_push
#print axioms OCaml.Vm.Sim.push_loaded
#print axioms Vsa.Sim.pushacc0_code_store
#print axioms Vsa.Sim.tr_pushacc0
#print axioms OCaml.Vm.Sim.pushacc0_loaded
#print axioms Vsa.Sim.pushacc1_code_store
#print axioms Vsa.Sim.tr_pushacc1
#print axioms OCaml.Vm.Sim.pushacc1_loaded

-- Closure offsets preserve allocation identity, including signed displacements.
#print axioms OCaml.Vm.Sim.pointer_offset_word
#print axioms OCaml.Vm.Sim.signed_index_word
#print axioms OCaml.Vm.Sim.ClosureOffset.root
#print axioms OCaml.Vm.Sim.ClosureOffset.sourceWord
#print axioms OCaml.Vm.Sim.ClosureOffset.resultWord
#print axioms OCaml.Vm.Sim.offsetclosurem3_loaded
#print axioms Vsa.Sim.tr_offsetclosurem3
#print axioms OCaml.Vm.Sim.offsetclosurem3_arm
#print axioms OCaml.Vm.Sim.offsetclosure0_loaded
#print axioms Vsa.Sim.tr_offsetclosure0
#print axioms OCaml.Vm.Sim.offsetclosure0_arm
#print axioms OCaml.Vm.Sim.offsetclosure3_loaded
#print axioms Vsa.Sim.tr_offsetclosure3
#print axioms OCaml.Vm.Sim.offsetclosure3_arm
#print axioms OCaml.Vm.Sim.offsetclosure_loaded
#print axioms Vsa.Sim.tr_offsetclosure
#print axioms OCaml.Vm.Sim.offsetclosure_arm

#print axioms OCaml.Vm.Sim.stack_integer_word
#print axioms OCaml.Vm.Sim.value_byte_index
#print axioms OCaml.Vm.Sim.byte_tag
#print axioms OCaml.Vm.Sim.ByteSelection.sourceWord
#print axioms OCaml.Vm.Sim.ByteSelection.read
#print axioms OCaml.Vm.Sim.getbyteschar_loaded
#print axioms OCaml.Vm.Sim.getstringchar_loaded
#print axioms Vsa.Sim.tr_getbyteschar
#print axioms Vsa.Sim.tr_getstringchar
#print axioms OCaml.Vm.Sim.getbyteschar_arm
#print axioms OCaml.Vm.Sim.getstringchar_arm
#print axioms OCaml.Vm.Sim.value_index_word
#print axioms OCaml.Vm.Sim.getvectitem_loaded
#print axioms Vsa.Sim.tr_getvectitem
#print axioms OCaml.Vm.Sim.getvectitem_arm
#print axioms OCaml.Vm.Sim.pop_loaded
#print axioms Vsa.Sim.tr_pop
#print axioms OCaml.Vm.Sim.pop_arm
#print axioms OCaml.Vm.Sim.pop_step_arm
#print axioms OCaml.Vm.Sim.consume_value_restore
#print axioms OCaml.Vm.Sim.consume_value_arm
#print axioms OCaml.Vm.Sim.consume_restore
#print axioms OCaml.Vm.Sim.consume_arm
#print axioms OCaml.Vm.Sim.tag_add
#print axioms OCaml.Vm.Sim.tag_untag_odd

-- Shared low-six-bit shift count and generated shift arms.
#print axioms OCaml.Vm.Sim.shift_count
#print axioms OCaml.Vm.Sim.shiftLeft_native
#print axioms OCaml.Vm.Sim.shiftRight_native
#print axioms OCaml.Vm.Sim.shiftArith_native
#print axioms OCaml.Vm.Sim.tag_sub_one_even
#print axioms OCaml.Vm.Sim.left_shift_odd
#print axioms Vsa.Sim.tr_lslint
#print axioms OCaml.Vm.Sim.lslint_loaded
#print axioms OCaml.Vm.Sim.lslint_arm
#print axioms OCaml.Vm.Sim.lslint_step_arm
#print axioms Vsa.Sim.tr_lsrint
#print axioms OCaml.Vm.Sim.lsrint_loaded
#print axioms OCaml.Vm.Sim.lsrint_arm
#print axioms OCaml.Vm.Sim.lsrint_step_arm
#print axioms Vsa.Sim.tr_asrint
#print axioms OCaml.Vm.Sim.asrint_loaded
#print axioms OCaml.Vm.Sim.asrint_arm
#print axioms OCaml.Vm.Sim.asrint_step_arm
#print axioms OCaml.Vm.Sim.intOp_next

-- Both native paths of all signed/unsigned integer comparisons.
#print axioms OCaml.Vm.Sim.native_sge
#print axioms OCaml.Vm.Sim.native_slt
#print axioms OCaml.Vm.Sim.native_uge
#print axioms OCaml.Vm.Sim.native_ult
#print axioms OCaml.Vm.Sim.cmpOp_next
#print axioms Vsa.Sim.tr_ltint_true
#print axioms OCaml.Vm.Sim.ltint_true_loaded
#print axioms OCaml.Vm.Sim.ltint_true_arm
#print axioms Vsa.Sim.tr_ltint_false
#print axioms OCaml.Vm.Sim.ltint_false_loaded
#print axioms OCaml.Vm.Sim.ltint_false_arm
#print axioms OCaml.Vm.Sim.ltint_step_arm
#print axioms Vsa.Sim.tr_leint_true
#print axioms OCaml.Vm.Sim.leint_true_loaded
#print axioms OCaml.Vm.Sim.leint_true_arm
#print axioms Vsa.Sim.tr_leint_false
#print axioms OCaml.Vm.Sim.leint_false_loaded
#print axioms OCaml.Vm.Sim.leint_false_arm
#print axioms OCaml.Vm.Sim.leint_step_arm
#print axioms Vsa.Sim.tr_gtint_true
#print axioms OCaml.Vm.Sim.gtint_true_loaded
#print axioms OCaml.Vm.Sim.gtint_true_arm
#print axioms Vsa.Sim.tr_gtint_false
#print axioms OCaml.Vm.Sim.gtint_false_loaded
#print axioms OCaml.Vm.Sim.gtint_false_arm
#print axioms OCaml.Vm.Sim.gtint_step_arm
#print axioms Vsa.Sim.tr_geint_true
#print axioms OCaml.Vm.Sim.geint_true_loaded
#print axioms OCaml.Vm.Sim.geint_true_arm
#print axioms Vsa.Sim.tr_geint_false
#print axioms OCaml.Vm.Sim.geint_false_loaded
#print axioms OCaml.Vm.Sim.geint_false_arm
#print axioms OCaml.Vm.Sim.geint_step_arm
#print axioms Vsa.Sim.tr_ultint_true
#print axioms OCaml.Vm.Sim.ultint_true_loaded
#print axioms OCaml.Vm.Sim.ultint_true_arm
#print axioms Vsa.Sim.tr_ultint_false
#print axioms OCaml.Vm.Sim.ultint_false_loaded
#print axioms OCaml.Vm.Sim.ultint_false_arm
#print axioms OCaml.Vm.Sim.ultint_step_arm
#print axioms Vsa.Sim.tr_ugeint_true
#print axioms OCaml.Vm.Sim.ugeint_true_loaded
#print axioms OCaml.Vm.Sim.ugeint_true_arm
#print axioms Vsa.Sim.tr_ugeint_false
#print axioms OCaml.Vm.Sim.ugeint_false_loaded
#print axioms OCaml.Vm.Sim.ugeint_false_arm
#print axioms OCaml.Vm.Sim.ugeint_step_arm
#print axioms Vsa.Sim.tr_addint
#print axioms OCaml.Vm.Sim.addint_loaded
#print axioms OCaml.Vm.Sim.addint_arm
#print axioms OCaml.Vm.Sim.addint_step_arm
#print axioms Vsa.Sim.tr_subint
#print axioms OCaml.Vm.Sim.subint_loaded
#print axioms OCaml.Vm.Sim.subint_arm
#print axioms OCaml.Vm.Sim.subint_step_arm
#print axioms Vsa.Sim.tr_andint
#print axioms OCaml.Vm.Sim.andint_loaded
#print axioms OCaml.Vm.Sim.andint_arm
#print axioms OCaml.Vm.Sim.andint_step_arm
#print axioms Vsa.Sim.tr_orint
#print axioms OCaml.Vm.Sim.orint_loaded
#print axioms OCaml.Vm.Sim.orint_arm
#print axioms OCaml.Vm.Sim.orint_step_arm
#print axioms Vsa.Sim.tr_xorint
#print axioms OCaml.Vm.Sim.xorint_loaded
#print axioms OCaml.Vm.Sim.xorint_arm
#print axioms OCaml.Vm.Sim.xorint_step_arm
#print axioms OCaml.Vm.Sim.tag_eq_false
#print axioms OCaml.Vm.Sim.false_word_iff
#print axioms Vsa.Sim.tr_branchif_jump
#print axioms OCaml.Vm.Sim.branchif_jump_loaded
#print axioms OCaml.Vm.Sim.branchif_jump_arm
#print axioms Vsa.Sim.tr_branchif_next
#print axioms OCaml.Vm.Sim.branchif_next_loaded
#print axioms OCaml.Vm.Sim.branchif_next_arm
#print axioms OCaml.Vm.Sim.branchif_arm
#print axioms Vsa.Sim.tr_branchifnot_jump
#print axioms OCaml.Vm.Sim.branchifnot_jump_loaded
#print axioms OCaml.Vm.Sim.branchifnot_jump_arm
#print axioms Vsa.Sim.tr_branchifnot_next
#print axioms OCaml.Vm.Sim.branchifnot_next_loaded
#print axioms OCaml.Vm.Sim.branchifnot_next_arm
#print axioms OCaml.Vm.Sim.branchifnot_arm
#print axioms OCaml.Vm.Sim.codePc_add
#print axioms OCaml.Vm.Sim.tag_word32
#print axioms Vsa.Sim.tr_constint
#print axioms OCaml.Vm.Sim.constint_loaded
#print axioms OCaml.Vm.Sim.constint_arm
#print axioms OCaml.Vm.Sim.codePc_succ
#print axioms OCaml.Vm.Sim.immediate_restore
#print axioms OCaml.Vm.Sim.immediate_preserved
#print axioms OCaml.Vm.Sim.SwitchTag.of_object
#print axioms OCaml.Vm.Sim.SwitchTag.read
#print axioms OCaml.Vm.Sim.switch_count_read
#print axioms OCaml.Vm.Sim.switch_block_low_bit
#print axioms OCaml.Vm.Sim.switch_index_scale
#print axioms OCaml.Vm.Sim.switch_tag_step
#print axioms OCaml.Vm.Sim.switch_sizes_nat
#print axioms OCaml.Vm.Sim.switch_block_arm
#print axioms OCaml.Vm.Sim.switch_block_step_arm

#print axioms OCaml.Vm.Sim.tag_low_bit
#print axioms OCaml.Vm.Sim.longVal_nonnegative
#print axioms OCaml.Vm.Sim.switch_int_scale
#print axioms OCaml.Vm.Sim.switch_table_word
#print axioms OCaml.Vm.Sim.switch_int_arm
#print axioms OCaml.Vm.Sim.switch_int_step_arm

#print axioms Vsa.Sim.tr_switch_int
#print axioms Vsa.Sim.tr_switch_block
#print axioms OCaml.Vm.Sim.switch_int_loaded
#print axioms OCaml.Vm.Sim.switch_block_loaded

#print axioms OCaml.Vm.Sim.word_after_writeLog_at
#print axioms OCaml.Vm.Sim.image_entry_code
#print axioms OCaml.Vm.Sim.stack_decrement
#print axioms OCaml.Vm.Sim.retaddr_stored
#print axioms OCaml.Vm.Sim.retaddr_roots
#print axioms OCaml.Vm.Sim.retaddr_payload
#print axioms OCaml.Vm.Sim.retaddr_extra_word
#print axioms OCaml.Vm.Sim.retaddr_log_in
#print axioms OCaml.Vm.Sim.retaddr_restore
#print axioms OCaml.Vm.Sim.push_retaddr_arm
#print axioms OCaml.Vm.Sim.push_retaddr_step_arm

#print axioms OCaml.Vm.Sim.heap_set_here
#print axioms OCaml.Vm.Sim.heap_set_other
#print axioms OCaml.Vm.Sim.live_field_edit
#print axioms OCaml.Vm.Sim.heap_set_size
#print axioms OCaml.Vm.Sim.heap_field_edit
#print axioms OCaml.Vm.Sim.block_field_written
#print axioms OCaml.Vm.Sim.field_log_outside
#print axioms OCaml.Vm.Sim.heap_field_written
#print axioms OCaml.Vm.Sim.payload_heap_frame
#print axioms OCaml.Vm.Sim.payload_field_written
#print axioms OCaml.Vm.Sim.field_restore
#print axioms OCaml.Vm.Sim.offsetref_arm
#print axioms OCaml.Vm.Sim.offsetref_step_arm

#print axioms Vsa.Sim.tr_offsetref
#print axioms OCaml.Vm.Sim.offsetref_loaded
#print axioms OCaml.Vm.Sim.payload_rebuild
#print axioms OCaml.Vm.Sim.heap_frame_log
#print axioms OCaml.Vm.Sim.stack_frame_log
#print axioms OCaml.Vm.Sim.payload_trap_written
#print axioms OCaml.Vm.Sim.trap_restore
#print axioms OCaml.Vm.Sim.nat_shift_word
#print axioms OCaml.Vm.Sim.trap_link_nonnegative
#print axioms OCaml.Vm.Sim.poptrap_link
#print axioms OCaml.Vm.Sim.poptrap_arm
#print axioms OCaml.Vm.Sim.poptrap_step_arm
#print axioms Vsa.Sim.tr_poptrap
#print axioms OCaml.Vm.Sim.poptrap_loaded
#print axioms OCaml.Vm.Sim.trap_shift_words
#print axioms OCaml.Vm.Sim.pushtrap_link
#print axioms OCaml.Vm.Sim.pushtrap_stored
#print axioms OCaml.Vm.Sim.pushtrap_roots
#print axioms OCaml.Vm.Sim.pushtrap_payload
#print axioms OCaml.Vm.Sim.pushtrap_log_in
#print axioms OCaml.Vm.Sim.heap_of_live
#print axioms OCaml.Vm.Sim.live_env_of_root
#print axioms OCaml.Vm.Sim.payload_env_of_root
#print axioms OCaml.Vm.Sim.payload_extra
#print axioms OCaml.Vm.Sim.SignalCheckReady.read32
#print axioms OCaml.Vm.Sim.SignalCheckReady.read
#print axioms OCaml.Vm.Sim.sign_extend_nat32
#print axioms OCaml.Vm.Sim.apply_count_word
#print axioms Vsa.Sim.tr_apply
#print axioms OCaml.Vm.Sim.apply_loaded
#print axioms Vsa.Sim.tr_apply1
#print axioms OCaml.Vm.Sim.apply1_loaded
#print axioms Vsa.Sim.tr_apply2
#print axioms OCaml.Vm.Sim.apply2_loaded
#print axioms Vsa.Sim.tr_apply3
#print axioms OCaml.Vm.Sim.apply3_loaded
#print axioms OCaml.Vm.Sim.range_disjoint_inside
#print axioms OCaml.Vm.Sim.outLRange_of_windows
#print axioms OCaml.Vm.Sim.indexed_log_outside
#print axioms OCaml.Vm.Sim.indexed_log_read
#print axioms OCaml.Vm.Sim.indexed_stored
#print axioms OCaml.Vm.Sim.indexed_log_in
#print axioms OCaml.Vm.Sim.apply_order_distinct
#print axioms OCaml.Vm.Sim.apply_order_member
#print axioms OCaml.Vm.Sim.apply_entries_distinct
#print axioms OCaml.Vm.Sim.apply_entries_selected
#print axioms OCaml.Vm.Sim.apply_entries_in
#print axioms OCaml.Vm.Sim.ValueWords.nil
#print axioms OCaml.Vm.Sim.ValueWords.cons
#print axioms OCaml.Vm.Sim.ValueWords.append
#print axioms OCaml.Vm.Sim.stack_value_words
#print axioms OCaml.Vm.Sim.apply_frame_roots
#print axioms OCaml.Vm.Sim.apply_frame_payload
#print axioms OCaml.Vm.Sim.EnterOutside.sublist
#print axioms OCaml.Vm.Sim.SignalCheckReady.read_log
#print axioms OCaml.Vm.Sim.StackEditOutside.accu_field_load
#print axioms OCaml.Vm.Sim.apply_frame_restore
#print axioms OCaml.Vm.Sim.apply1_arm
#print axioms OCaml.Vm.Sim.apply2_arm
#print axioms OCaml.Vm.Sim.apply3_arm
#print axioms OCaml.Vm.Sim.apply1_step_arm
#print axioms OCaml.Vm.Sim.apply2_step_arm
#print axioms OCaml.Vm.Sim.apply3_step_arm
#print axioms Vsa.Sim.tr_grab_fast
#print axioms OCaml.Vm.Sim.grab_fast_loaded
#print axioms OCaml.Vm.Sim.nonnegative_word32
#print axioms OCaml.Vm.Sim.grab_fast_guard
#print axioms OCaml.Vm.Sim.grab_fast_extra
#print axioms OCaml.Vm.Sim.grab_fast_arm
#print axioms OCaml.Vm.Sim.grab_fast_step_arm
#print axioms Vsa.Sim.tr_appterm_prefix
#print axioms OCaml.Vm.Sim.appterm_prefix_loaded
#print axioms Vsa.Sim.tr_appterm_copy_more
#print axioms OCaml.Vm.Sim.appterm_copy_more_loaded
#print axioms Vsa.Sim.tr_appterm_copy_last
#print axioms OCaml.Vm.Sim.appterm_copy_last_loaded
#print axioms Vsa.Sim.tr_appterm_suffix
#print axioms OCaml.Vm.Sim.appterm_suffix_loaded
#print axioms OCaml.Vm.Sim.ValueWords.readback
#print axioms OCaml.Vm.Sim.log_in_windows_of_mem
#print axioms OCaml.Vm.Sim.value_log_length
#print axioms OCaml.Vm.Sim.value_log_getElem
#print axioms OCaml.Vm.Sim.reverse_copy_log_step
#print axioms OCaml.Vm.Sim.reverse_copy_log_initial
#print axioms OCaml.Vm.Sim.reverse_copy_log_words
#print axioms OCaml.Vm.Sim.reverse_copy_entry
#print axioms OCaml.Vm.Sim.reverse_copy_log_in
#print axioms OCaml.Vm.Sim.reverse_copy_source_outside
#print axioms OCaml.Vm.Sim.low32_nat
#print axioms OCaml.Vm.Sim.backward_counter_succ
#print axioms OCaml.Vm.Sim.backward_cursor_succ
#print axioms OCaml.Vm.Sim.backward_cursor_step
#print axioms OCaml.Vm.Sim.backward_counter_step
#print axioms OCaml.Vm.Sim.backward_counter_live
#print axioms OCaml.Vm.Sim.BackwardCopyAt.index
#print axioms OCaml.Vm.Sim.BackwardCopyAt.read
#print axioms OCaml.Vm.Sim.BackwardCopyAt.advance
#print axioms OCaml.Vm.Sim.BackwardCopyRegion.entry
#print axioms OCaml.Vm.Sim.backward_copy_loop
#print axioms OCaml.Vm.Sim.backward_copy_more
#print axioms OCaml.Vm.Sim.backward_copy_last
#print axioms OCaml.Vm.Sim.backward_copy_iteration
#print axioms OCaml.Vm.Sim.backward_copy_run
#print axioms OCaml.Vm.Sim.tailcall_restore_of_log
#print axioms OCaml.Vm.Sim.word32_nat_small
#print axioms OCaml.Vm.Sim.appterm_base_word
#print axioms OCaml.Vm.Sim.appterm_cursor_word
#print axioms OCaml.Vm.Sim.appterm_counter_word
#print axioms OCaml.Vm.Sim.appterm_prefix_guard
#print axioms OCaml.Vm.Sim.ApptermWriteOk.copy_after
#print axioms OCaml.Vm.Sim.appterm_setup
#print axioms OCaml.Vm.Sim.appterm_finish
#print axioms OCaml.Vm.Sim.appterm_arm
#print axioms OCaml.Vm.Sim.appterm_step_arm
#print axioms Vsa.Sim.tr_restart_prefix_more
#print axioms OCaml.Vm.Sim.restart_prefix_more_loaded
#print axioms Vsa.Sim.tr_restart_prefix_empty
#print axioms OCaml.Vm.Sim.restart_prefix_empty_loaded
#print axioms Vsa.Sim.tr_restart_copy_more
#print axioms OCaml.Vm.Sim.restart_copy_more_loaded
#print axioms Vsa.Sim.tr_restart_copy_last
#print axioms OCaml.Vm.Sim.restart_copy_last_loaded
#print axioms Vsa.Sim.tr_restart_suffix
#print axioms OCaml.Vm.Sim.restart_suffix_loaded
#print axioms OCaml.Vm.Sim.BlockSelection.sourceWord
#print axioms OCaml.Vm.Sim.BlockSelection.live
#print axioms OCaml.Vm.Sim.BlockSelection.header
#print axioms OCaml.Vm.Sim.BlockSelection.words
#print axioms OCaml.Vm.Sim.BlockSelection.field
#print axioms OCaml.Vm.Sim.BlockSelection.field_root
#print axioms OCaml.Vm.Sim.restart_restore
#print axioms OCaml.Vm.Sim.payload_replace_prefix
#print axioms OCaml.Vm.Sim.return_payload
#print axioms OCaml.Vm.Sim.return_frame_values
#print axioms OCaml.Vm.Sim.nat64_toInt
#print axioms OCaml.Vm.Sim.return_more_guard
#print axioms OCaml.Vm.Sim.extra_decrement
#print axioms Vsa.Sim.tr_return_more
#print axioms OCaml.Vm.Sim.return_more_loaded
#print axioms Vsa.Sim.tr_return_frame
#print axioms OCaml.Vm.Sim.return_frame_loaded
#print axioms OCaml.Vm.Sim.return_more_arm
#print axioms OCaml.Vm.Sim.return_frame_arm
#print axioms OCaml.Vm.Sim.return_more_step_arm
#print axioms OCaml.Vm.Sim.return_frame_step_arm
#print axioms OCaml.Vm.Sim.apply_arm
#print axioms OCaml.Vm.Sim.apply_step_arm
#print axioms OCaml.Vm.Sim.pushtrap_arm
#print axioms OCaml.Vm.Sim.pushtrap_step_arm
#print axioms OCaml.Vm.Sim.pushtrap_restore
#print axioms Vsa.Sim.tr_pushtrap
#print axioms OCaml.Vm.Sim.pushtrap_loaded
#print axioms Vsa.Sim.tr_push_retaddr
#print axioms OCaml.Vm.Sim.push_retaddr_loaded
#print axioms OCaml.Vm.Sim.stack_prepend
#print axioms OCaml.Vm.Sim.payload_stack_prepend

#print axioms Vsa.Sim.tr_check_signals
#print axioms OCaml.Vm.Sim.check_signals_loaded
#print axioms OCaml.Vm.Sim.signalCheckReady_of_runtime
#print axioms OCaml.Vm.Sim.check_signals_arm
#print axioms OCaml.Vm.Sim.check_signals_step_arm

#print axioms OCaml.Vm.Sim.mulint_setup
#print axioms OCaml.Vm.Sim.mulint_callee
#print axioms OCaml.Vm.Sim.mulint_return
#print axioms OCaml.Vm.Sim.mulint_arm
#print axioms OCaml.Vm.Sim.mulint_step_arm

#print axioms OCaml.Vm.Sim.muldi3_loaded
#print axioms OCaml.Vm.Sim.muldi3_post_named
#print axioms OCaml.Vm.Sim.muldi3_summary
#print axioms OCaml.Vm.Sim.tag_truncate
#print axioms OCaml.Vm.Sim.tag_mul_native

#print axioms Vsa.Sim.tr_mulint_prefix
#print axioms Vsa.Sim.tr_mulint_suffix
#print axioms OCaml.Vm.Sim.mulint_prefix_loaded
#print axioms OCaml.Vm.Sim.mulint_suffix_loaded

#print axioms Vsa.Sim.tr_offsetint
#print axioms OCaml.Vm.Sim.offsetint_loaded
#print axioms OCaml.Vm.Sim.offsetintOperand_large
#print axioms OCaml.Vm.Sim.offsetint_width_obstruction
#print axioms OCaml.Vm.Sim.offsetintOperand_eq
#print axioms OCaml.Vm.Sim.tag_offsetint
#print axioms OCaml.Vm.Sim.offsetintOperand_model
#print axioms OCaml.Vm.Sim.offsetint_arm
#print axioms OCaml.Vm.Sim.offsetint_step_arm
#print axioms OCaml.Vm.Sim.tag_sub
#print axioms OCaml.Vm.Sim.tag_not
#print axioms Vsa.Sim.tr_boolnot
#print axioms OCaml.Vm.Sim.boolnot_loaded
#print axioms OCaml.Vm.Sim.boolnot_arm
#print axioms OCaml.Vm.Sim.tag_neg
#print axioms OCaml.Vm.Sim.untag_tag
#print axioms OCaml.Vm.Sim.untag_neg
#print axioms OCaml.Vm.Sim.negint_arm

-- Primitive-name binding is necessary at the loaded cut.
#print axioms OCaml.Vm.Sim.PrimitiveBinding.loaded_prims
#print axioms OCaml.Vm.Sim.PrimitiveBinding.primitive_binding_obstruction
-- Primitive bindings strengthen entry/loop data and survive memory frames.
#print axioms OCaml.Vm.PrimitiveBindings.of_words
#print axioms OCaml.Vm.PrimitiveBindings.get
#print axioms OCaml.Vm.PrimitiveBindings.frame
#print axioms OCaml.Loaded.primitives
#print axioms OCaml.Vm.Sim.PrimitiveBinding.loaded_forget_primitives
#print axioms OCaml.Vm.Sim.PrimitiveBinding.loaded_probes_disjoint
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_register_named_value
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_open_descriptor_out
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_open_descriptor_in
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_out_channels_list
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_flush
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_output_char
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_output
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_output_bytes
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_format_int
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_string_length
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_ml_bytes_length
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_string_equal
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_string_notequal
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_int64_float_of_bits
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_naked_pointers_checked
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_big_endian
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_word_size
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_int_size
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_max_wosize
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_ostype_unix
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_ostype_win32
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_ostype_cygwin
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_const_backend_type
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_get_config
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_executable_name
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_argv
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_get_argv
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_int_compare
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_fresh_oo_id
#print axioms OCaml.Vm.PrimitiveEntries.entry_caml_sys_exit

#print axioms Vsa.Sim.Boot.writeLog_view
#print axioms Vsa.Sim.Boot.loaderMem_get
#print axioms Vsa.Sim.Boot.observedMem_get
#print axioms Vsa.Sim.Boot.LogOk.of_checks
#print axioms OCaml.Vm.Boot.WhileMinLog.logOk
#print axioms OCaml.Vm.Boot.WhileMinLog.memory_view

#print axioms Vsa.Sim.Boot.bytesT_view
#print axioms Vsa.Sim.Boot.observedMem_bytes

#print axioms OCaml.Vm.Boot.HeapClosed.live_defined
#print axioms OCaml.Vm.Boot.HeapImage.repr

#print axioms Vsa.Sim.Boot.observedMem_bytes_stored
#print axioms Vsa.Sim.Boot.bytesT_memEqv
#print axioms OCaml.Vm.Boot.WhileMinRuntime.fields
#print axioms OCaml.Vm.Boot.WhileMinRuntime.freeList
#print axioms OCaml.Vm.Boot.WhileMinRuntime.runtimeOk
#print axioms OCaml.Vm.Boot.WhileMinRuntime.runtimeOk_fillZero

#print axioms OCaml.Vm.Boot.list_get_of_fin
#print axioms OCaml.Vm.Boot.WhileMinHeap.objects
#print axioms OCaml.Vm.Boot.WhileMinHeap.closed
#print axioms OCaml.Vm.Boot.WhileMinHeap.separated
#print axioms OCaml.Vm.Boot.WhileMinHeap.image
#print axioms OCaml.Vm.Boot.WhileMinHeap.repr
#print axioms OCaml.Vm.Boot.WhileMinEntry.code
#print axioms OCaml.Vm.Boot.WhileMinEntry.loaded
#print axioms OCaml.Vm.Boot.WhileMinEntry.EntryControl.fillZero
#print axioms OCaml.Vm.Boot.WhileMinEntry.loaded_fillZero
-- Read-only roots, total scalar observations and string-length contracts.
#print axioms OCaml.Vm.Primitives.VmPayload.accu_of_root
#print axioms OCaml.Vm.Primitives.VmPayload.object_at
#print axioms OCaml.Vm.Primitives.readOnly_contract
#print axioms OCaml.Vm.Primitives.read8_pins
#print axioms OCaml.Vm.Primitives.read8_value
#print axioms OCaml.Vm.Primitives.byte_total
#print axioms OCaml.Vm.Primitives.stringLengthWord_tag
#print axioms OCaml.Vm.Primitives.StringInput.shape
#print axioms OCaml.Vm.Primitives.string_length_contract
#print axioms OCaml.Vm.Primitives.caml_sys_argv_primitive
#print axioms OCaml.Vm.Primitives.caml_ml_string_length_primitive
#print axioms OCaml.Vm.Primitives.caml_ml_bytes_length_primitive

#print axioms OCaml.Vm.Primitives.singleton_chain_facts
#print axioms OCaml.Vm.Primitives.return_facts
#print axioms OCaml.Vm.Primitives.readonly_wlog
#print axioms OCaml.Vm.Primitives.readonly_log
#print axioms OCaml.Vm.Primitives.readonly_facts_append
#print axioms OCaml.Vm.Primitives.memory_free_facts
#print axioms OCaml.Vm.Primitives.access_then_free_facts
#print axioms OCaml.Vm.Primitives.ReadWindow.ld
#print axioms OCaml.Vm.Primitives.ReadWindow.lbu

-- Mutable global effects and representation frames.
#print axioms OCaml.Vm.Primitives.image_of_writeLog
#print axioms OCaml.Vm.Primitives.EffectPost.loop
#print axioms OCaml.Vm.Primitives.write_of_blocks
#print axioms OCaml.Vm.Primitives.copied_of_writeLog
#print axioms OCaml.Vm.Primitives.object_copied
#print axioms OCaml.Vm.Primitives.channel_copied
#print axioms OCaml.Vm.Primitives.VmPayload.frame_log
#print axioms OCaml.Vm.Primitives.VmPayload.ooId
#print axioms OCaml.Vm.Primitives.WriteWindow.sd
#print axioms OCaml.Vm.Primitives.word_writeLog
#print axioms OCaml.Vm.Primitives.counterWord_succ
#print axioms OCaml.Vm.Primitives.counterWord_repr
#print axioms OCaml.Vm.Primitives.counter_contract
#print axioms OCaml.Vm.Primitives.caml_fresh_oo_id_primitive

#print axioms OCaml.Vm.Primitives.bindings_frame_log
#print axioms OCaml.Vm.Primitives.word_byte_extract
#print axioms OCaml.Vm.Primitives.words_copied
#print axioms OCaml.Vm.Primitives.PaddedString.eq_of_words
#print axioms OCaml.Vm.Primitives.PaddedString.copied
#print axioms OCaml.Vm.Primitives.PaddedString.eq_iff_words
#print axioms OCaml.Vm.Boot.WhileMinLog.fin_none_below
#print axioms OCaml.Vm.Boot.WhileMinLog.memory_below
#print axioms OCaml.Vm.Boot.WhileMinImage.initial_text
#print axioms OCaml.Vm.Boot.WhileMinImage.initial_rodata
#print axioms OCaml.Vm.Boot.WhileMinImage.observed_text
#print axioms OCaml.Vm.Boot.WhileMinImage.observed_rodata
#print axioms OCaml.Vm.Boot.WhileMinImage.executable
#print axioms OCaml.Vm.Boot.WhileMinRegisters.assignments_distinct
#print axioms OCaml.Vm.Boot.WhileMinRegisters.register_get
#print axioms OCaml.Vm.Boot.WhileMinRegisters.good_state
#print axioms OCaml.Vm.Boot.PrimitiveRowAt.binding
#print axioms OCaml.Vm.Boot.WhileMinPrimitives.bindings
#print axioms OCaml.Vm.Boot.WhileMin.memory_eq
#print axioms OCaml.Vm.Boot.WhileMin.control
#print axioms OCaml.Vm.Boot.WhileMin.loaded
#print axioms OCaml.Vm.Boot.WhileMin.loaded_fillZero

#print axioms OCaml.Vm.Boot.WhileMin.memory_equiv

-- Canonical string equality: generated CFG and total word-loop fold.
#print axioms OCaml.Vm.Primitives.holds_select
#print axioms OCaml.Vm.Primitives.holds_project
#print axioms OCaml.Vm.Primitives.boundary_of_blocks
#print axioms OCaml.Vm.Primitives.BoundaryPost.then
#print axioms OCaml.Vm.Primitives.BoundaryPost.finish
#print axioms OCaml.Vm.Primitives.boundary_bind
#print axioms OCaml.Vm.Primitives.WordRange.window
#print axioms OCaml.Vm.Primitives.scanPtr_delta
#print axioms OCaml.Vm.Primitives.header_words
#print axioms OCaml.Vm.Primitives.StringScan.scan_iteration
#print axioms OCaml.Vm.Primitives.StringScan.scan_loop
#print axioms OCaml.Vm.Primitives.StringScan.scan_words
#print axioms OCaml.Vm.Primitives.StringScan.string_equal_machine
#print axioms OCaml.Vm.Primitives.string_comparison_value
#print axioms OCaml.Vm.Primitives.string_equal_contract
#print axioms OCaml.Vm.Primitives.caml_string_equal_primitive

-- Full JAL bridge and represented string inequality wrapper.
#print axioms OCaml.Vm.Primitives.BlockPost.effect
#print axioms OCaml.Vm.Primitives.registers_of_blocks
#print axioms OCaml.Vm.Primitives.EffectPost.trans
#print axioms OCaml.Vm.Primitives.EffectPost.widen
#print axioms OCaml.Vm.Primitives.call_observed
#print axioms OCaml.Vm.Primitives.call_summary
#print axioms OCaml.Vm.Primitives.call_registers_summary
#print axioms OCaml.Vm.Primitives.native_save_address
#print axioms OCaml.Vm.Primitives.savedRa_value
#print axioms OCaml.Vm.Primitives.summary_bind
#print axioms OCaml.Vm.Primitives.PaddedString.frame_log
#print axioms OCaml.Vm.Primitives.StringWrapper.save_summary
#print axioms OCaml.Vm.Primitives.StringWrapper.restore_summary
#print axioms OCaml.Vm.Primitives.wrapper_enter
#print axioms OCaml.Vm.Primitives.wrapper_equal
#print axioms OCaml.Vm.Primitives.wrapper_leave
#print axioms OCaml.Vm.Primitives.string_notequal_machine
#print axioms OCaml.Vm.Primitives.string_complement
#print axioms OCaml.Vm.Primitives.string_notequal_contract
#print axioms OCaml.Vm.Primitives.caml_string_notequal_primitive
#print axioms Vsa.Sim.bridgeOfSegFull

-- Allocation transport and generated double nursery fast path.
#print axioms OCaml.Vm.Primitives.VmPayload.live_bound
#print axioms OCaml.Vm.Primitives.live_after_alloc
#print axioms OCaml.Vm.Primitives.VmPayload.allocate
#print axioms OCaml.Vm.Primitives.allocation_contract
#print axioms OCaml.Vm.Primitives.bytesT_writeLog_out
#print axioms OCaml.Vm.Primitives.DoubleAllocation.reserve_summary
#print axioms OCaml.Vm.Primitives.DoubleAllocation.initialize_summary
#print axioms OCaml.Vm.Primitives.DoubleAllocation.copy_double_fast
#print axioms OCaml.Vm.Primitives.DoubleAllocation.field_address
#print axioms OCaml.Vm.Primitives.DoubleAllocation.double_layout

-- callback.c named-root replacement and C-string keys.
#print axioms OCaml.Bytecode.registerNamedValue_lookup
#print axioms OCaml.Bytecode.registerNamedValue_lookup_other
#print axioms OCaml.Bytecode.registerNamedValue_member
#print axioms OCaml.Bytecode.named_replacement_check
#print axioms OCaml.Bytecode.named_first_nul_check
#print axioms OCaml.Bytecode.named_primitive_replacement

-- G1 boxed int64 bit reinterpretation through the nursery allocator.
#print axioms OCaml.Vm.Primitives.BoundaryPost.then_write
#print axioms OCaml.Vm.Primitives.DoubleAllocation.FastMemory.frame
#print axioms OCaml.Vm.Primitives.Int64FloatTail.summary
#print axioms OCaml.Vm.Primitives.int64_float_machine
#print axioms OCaml.Vm.Primitives.int64_float_contract
#print axioms OCaml.Vm.Primitives.caml_int64_float_of_bits_primitive

#print axioms OCaml.Vm.Primitives.boundedRank_spec
#print axioms OCaml.Vm.Primitives.localRun_triple
#print axioms OCaml.Vm.Primitives.symbolic_summary
#print axioms OCaml.Vm.Primitives.strlen_symbolic
#print axioms OCaml.Vm.Primitives.strlen_summary
#print axioms OCaml.Vm.Primitives.strlen_memory

#print axioms OCaml.Vm.Primitives.copied_of_observedLog
#print axioms OCaml.Vm.Primitives.VmPayload.frame_observedLog
#print axioms OCaml.Vm.Primitives.VmPayload.frame_observed
#print axioms OCaml.Vm.Primitives.some_of_observed
#print axioms OCaml.Vm.Primitives.library_pc
#print axioms OCaml.Vm.Primitives.library_gpr
#print axioms OCaml.Vm.Primitives.library_register_frame
#print axioms OCaml.Vm.Primitives.bindings_observed
#print axioms OCaml.Vm.Primitives.fixedBytes_observed
#print axioms OCaml.Vm.Primitives.image_observed
#print axioms OCaml.Vm.Primitives.strlen_leaf
#print axioms OCaml.Vm.Primitives.strlen_result

#print axioms OCaml.Vm.Primitives.accessPlan_facts
#print axioms OCaml.Vm.Primitives.SmallAllocation.reserve_summary
#print axioms OCaml.Vm.Primitives.SmallAllocation.initialize_summary
#print axioms OCaml.Vm.Primitives.StringAllocation.prepare_summary
#print axioms OCaml.Vm.Primitives.StringAllocation.reserve_summary
#print axioms OCaml.Vm.Primitives.StringAllocation.initialize_summary
#print axioms OCaml.Vm.Primitives.StringAllocation.prepare_eval
#print axioms OCaml.Vm.Primitives.StringAllocation.reserve_eval
#print axioms OCaml.Vm.Primitives.StringAllocation.initialize_eval
#print axioms OCaml.Vm.Primitives.StringAllocation.prepare_access
#print axioms OCaml.Vm.Primitives.StringAllocation.reserve_access
#print axioms OCaml.Vm.Primitives.StringAllocation.prepare_log
#print axioms OCaml.Vm.Primitives.StringAllocation.reserve_log
#print axioms OCaml.Vm.Primitives.StringAllocation.initialize_log
#print axioms OCaml.Vm.Primitives.StringAllocation.prepare_fast
#print axioms OCaml.Vm.Primitives.StringAllocation.reserve_fast
#print axioms OCaml.Vm.Primitives.StringAllocation.initialize_fast

#print axioms OCaml.Vm.Primitives.WriteWindow.sb
#print axioms OCaml.Vm.Primitives.StringAllocation.initialize_access
#print axioms OCaml.Vm.Primitives.StringAllocation.alloc_string_nursery
#print axioms OCaml.Vm.Primitives.StringAllocation.nursery_readback

#print axioms Vsa.Sim.writeMap8_get_byte
#print axioms Vsa.Sim.writeMap8_ld_byte
#print axioms VsaIris.Memcpy.memcpyLocalRun
#print axioms OCaml.Vm.Primitives.image_local
#print axioms OCaml.Vm.Primitives.copyResult_of_library
#print axioms OCaml.Vm.Primitives.memcpy_summary

#print axioms OCaml.Vm.Primitives.RegistersPost.vsaOk
#print axioms OCaml.Vm.Primitives.StringAllocation.stringWords_toNat
#print axioms OCaml.Vm.Primitives.StringAllocation.stringSpan_toNat
#print axioms OCaml.Vm.Primitives.StringAllocation.stringHeader_ok
#print axioms OCaml.Vm.Primitives.StringAllocation.paddingWord_toNat
#print axioms OCaml.Vm.Primitives.StringAllocation.shell_layout
#print axioms OCaml.Vm.Primitives.StringAllocation.StringShell.object
#print axioms OCaml.Vm.Primitives.StringAllocation.StringShell.padded

#print axioms OCaml.Vm.Primitives.StringAllocation.initialization_shell_log
#print axioms OCaml.Vm.Primitives.StringAllocation.NurseryPost.shell
#print axioms OCaml.Vm.Primitives.StringAllocation.StringShell.frame_payload

#print axioms OCaml.Vm.Primitives.StringCopy.save_fast
#print axioms OCaml.Vm.Primitives.StringCopy.size_fast
#print axioms OCaml.Vm.Primitives.StringCopy.arguments_fast
#print axioms OCaml.Vm.Primitives.StringCopy.restore_fast
-- Startup summaries: generated blocks/calls and counted BSS loop.
#print axioms OCaml.Vm.Boot.Startup.setup_input
#print axioms OCaml.Vm.Boot.Startup.setup_summary
#print axioms OCaml.Vm.Boot.Startup.clear_input
#print axioms OCaml.Vm.Boot.Startup.clear_summary
#print axioms OCaml.Vm.Boot.Startup.clear_log
#print axioms OCaml.Vm.Boot.Startup.clear_regs
#print axioms OCaml.Vm.Boot.Startup.clear_body
#print axioms OCaml.Vm.Boot.Startup.guard_input
#print axioms OCaml.Vm.Boot.Startup.guard_summary
#print axioms OCaml.Vm.Boot.Startup.ClearRegion.cursor_nat
#print axioms OCaml.Vm.Boot.Startup.ClearRegion.window
#print axioms OCaml.Vm.Boot.Startup.ClearAt.index
#print axioms OCaml.Vm.Boot.Startup.clearWords_below
#print axioms OCaml.Vm.Boot.Startup.clear_iteration
#print axioms OCaml.Vm.Boot.Startup.clear_loop
#print axioms OCaml.Vm.Boot.Startup.bss_region
#print axioms OCaml.Vm.Boot.Startup.bss_end
#print axioms OCaml.Vm.Boot.Startup.setup_clear
#print axioms OCaml.Vm.Boot.Startup.args_input
#print axioms OCaml.Vm.Boot.Startup.crt0_to_call
#print axioms OCaml.Vm.Boot.Startup.crt0_to_main
#print axioms OCaml.Vm.Boot.Startup.CallPost.of_obs
#print axioms OCaml.Vm.Boot.Startup.call_80000038
#print axioms OCaml.Vm.Boot.Startup.call_80001dec
#print axioms OCaml.Vm.Boot.Startup.call_80001df4
#print axioms OCaml.Vm.Boot.Startup.main_input_bytes
#print axioms OCaml.Vm.Boot.Startup.main_prefix
#print axioms Vsa.Sim.Code._start_transport
#print axioms Vsa.Sim.Code.main_transport

#print axioms OCaml.Vm.Boot.Startup.main_log
#print axioms OCaml.Vm.Boot.Startup.main_to_caml_main
#print axioms OCaml.Vm.Boot.Startup.clearWords_above
#print axioms OCaml.Vm.Boot.Startup.read8_clearWords_above
#print axioms OCaml.Vm.Boot.Startup.crt0_to_caml_main
#print axioms OCaml.Vm.Primitives.EffectPost.gpr_frame
#print axioms OCaml.Vm.Primitives.EffectPost.observed_gpr
#print axioms OCaml.Vm.Primitives.EffectPost.readOnly_log
#print axioms Vsa.Densify.MemEqv.writeLog
#print axioms OCaml.Vm.Primitives.strlen_call
#print axioms OCaml.Vm.Primitives.StringAllocation.NurseryMetadata.frame_observedLog
#print axioms OCaml.Vm.Primitives.StringCopy.copy_string_sized
#print axioms OCaml.Vm.Primitives.StringCopy.copy_string_allocated
#print axioms OCaml.Vm.Primitives.StringCopy.caller_readback
#print axioms OCaml.Vm.Reloc.bytePayload_copyIn

#print axioms OCaml.Bytecode.executed_primitives_implemented

#print axioms OCaml.Vm.Boot.Startup.registersFactored.eq
#print axioms OCaml.Vm.Boot.Startup.registers_metadata
#print axioms OCaml.Vm.Boot.Startup.setupElf_congr
#print axioms OCaml.Vm.Boot.Startup.setupElf_pc
#print axioms OCaml.Vm.Boot.Startup.ElfReset.pc
#print axioms OCaml.Run.halts_after_iter
#print axioms OCaml.Run.div_after_iter
#print axioms OCaml.Bytecode.FwdReduction.equivalent
#print axioms OCaml.Bytecode.FwdObservations.of_common_result
#print axioms OCaml.Bytecode.FwdObservations.trans
#print axioms OCaml.Vm.Gc.ObservedAt.collect
#print axioms OCaml.Programs.LazyForce.tag_primitive
#print axioms OCaml.Programs.LazyForce.forward_get
#print axioms OCaml.Programs.LazyForce.force_tag
#print axioms OCaml.Programs.LazyForce.force_forward_test
#print axioms OCaml.Programs.LazyForce.force_forward_return
#print axioms OCaml.Programs.LazyForce.force_forward
#print axioms OCaml.Programs.LazyForce.force_value_test
#print axioms OCaml.Programs.LazyForce.force_value_return
#print axioms OCaml.Programs.LazyForce.force_value
#print axioms OCaml.Programs.LazyForce.force_observations
#print axioms OCaml.Programs.LazyForce.force_argument_edit
#print axioms OCaml.Programs.LazyForce.force_integer_observations
#print axioms OCaml.Programs.LazyForce.checked

#print axioms Vsa.Sim.pin8_of_last_write
#print axioms OCaml.Vm.Primitives.readonly_transport
#print axioms OCaml.Vm.Primitives.VmPayload.frame_outsideLog
#print axioms OCaml.Vm.Primitives.bindings_frame_outsideLog
#print axioms OCaml.Vm.Primitives.StringCopy.copy_string_finish
#print axioms OCaml.Vm.Primitives.StringCopy.copy_string_machine
#print axioms OCaml.Vm.Primitives.StringCopy.CopyPost.footprint
#print axioms OCaml.Vm.Primitives.StringCopy.CopyPost.memory_complete
#print axioms OCaml.Vm.Primitives.loop_of_abi_frame
#print axioms OCaml.Vm.Primitives.executable_name_machine
#print axioms OCaml.Vm.Primitives.executable_name_contract
#print axioms OCaml.Vm.Primitives.caml_sys_executable_name_primitive

#print axioms OCaml.Vm.Primitives.SmallAllocation.reserve_fast
#print axioms OCaml.Vm.Primitives.SmallAllocation.initialize_fast
#print axioms OCaml.Vm.Primitives.SmallAllocation.alloc_small_nursery
#print axioms OCaml.Vm.Primitives.SmallAllocation.blockHeader_ok
#print axioms OCaml.Vm.Primitives.SmallAllocation.NurseryPost.header
#print axioms OCaml.Vm.Primitives.ArgvTuple.prepare_summary
#print axioms OCaml.Vm.Primitives.ArgvTuple.prepare_call_decode
#print axioms OCaml.Vm.Primitives.ArgvTuple.allocate_summary
#print axioms OCaml.Vm.Primitives.ArgvTuple.allocate_call_decode
#print axioms OCaml.Vm.Primitives.ArgvTuple.finish_summary


#print axioms Vsa.Sim.execute_compare_char
#print axioms Vsa.Sim.runGM_append
#print axioms Vsa.Sim.wlogM_append
#print axioms OCaml.Vm.Primitives.StringCopy.CopyMemory.memory_transport
#print axioms OCaml.Vm.Primitives.StringCopy.CopyMemory.input
#print axioms OCaml.Vm.Primitives.ArgvTuple.prepare_log
#print axioms OCaml.Vm.Primitives.ArgvTuple.prepare_fast
#print axioms OCaml.Vm.Primitives.ArgvTuple.allocate_fast
#print axioms OCaml.Vm.Primitives.ArgvTuple.finish_fast

#print axioms Vsa.Sim.segmentSummary
-- Register initialization and primitive-lookup foundations.
#print axioms OCaml.Vm.Boot.Startup.choose_pure
#print axioms OCaml.Vm.Boot.Startup.initializeRegisters_values
#print axioms OCaml.Vm.Boot.Startup.registerWrites.program100
#print axioms OCaml.Vm.Boot.Startup.register_tail_run
#print axioms OCaml.Vm.Boot.Startup.initializeRegisters_program
#print axioms OCaml.Vm.Boot.Startup.initializeRegisters_run
#print axioms OCaml.Vm.Boot.Startup.initializeRegisters_preserves_memory
#print axioms OCaml.Vm.Boot.Startup.first_difference
#print axioms OCaml.Vm.Boot.Startup.isign_zero_iff
#print axioms OCaml.Vm.Boot.Startup.strcmpSign_zero_iff
#print axioms OCaml.Vm.Boot.Startup.spec_zero_streams
#print axioms OCaml.Vm.Boot.Startup.cstr_eq_of_streams
#print axioms OCaml.Vm.Boot.Startup.strcmpSpecSign_zero_iff
#print axioms OCaml.Vm.Boot.Startup.call_80024e34
#print axioms Vsa.Sim.RegisterWrites.run
#print axioms Vsa.Sim.RegisterWrites.run_apply
#print axioms Vsa.Sim.RegisterWrites.memory
#print axioms Vsa.Sim.RegisterWrites.output
#print axioms Vsa.Sim.RegisterWrites.cycles
#print axioms Vsa.Sim.Code.caml_build_primitive_table_transport
#print axioms Vsa.Sim.caml_build_primitive_tableX4e0cTRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e0cFRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e18Row
#print axioms Vsa.Sim.caml_build_primitive_tableX4e1cTRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e1cFRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e30Row
#print axioms Vsa.Sim.caml_build_primitive_tableX4e38TRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e38FRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e3cTRow
#print axioms Vsa.Sim.caml_build_primitive_tableX4e3cFRow

#print axioms OCaml.Vm.Gc.chainPlan_facts
#print axioms OCaml.Vm.Gc.PendingCopy.links
#print axioms OCaml.Vm.Gc.WorkQueue.View.first
#print axioms OCaml.Vm.Gc.WorkQueue.View.loadedNext
#print axioms OCaml.Vm.Gc.WorkQueue.body_tail
#print axioms OCaml.Vm.Gc.WorkQueue.body_frame
#print axioms OCaml.Vm.Gc.WorkQueue.pop
#print axioms OCaml.Vm.Gc.WorkQueue.pop_loaded
#print axioms OCaml.Vm.Gc.WorkQueue.todo_window
#print axioms OCaml.Vm.Gc.WorkQueue.head_access
#print axioms OCaml.Vm.Gc.WorkQueue.head_regs
#print axioms OCaml.Vm.Gc.WorkQueue.head_control
#print axioms OCaml.Vm.Gc.WorkQueue.child_access
#print axioms OCaml.Vm.Gc.WorkQueue.child_control
#print axioms OCaml.Vm.Gc.WorkQueue.pop_access
#print axioms OCaml.Vm.Gc.WorkQueue.pop_machine

#print axioms OCaml.Vm.Gc.word_writeLog_at
#print axioms OCaml.Vm.Gc.PendingCopy.of_links
#print axioms OCaml.Vm.Gc.WorkQueue.body_cons
#print axioms OCaml.Vm.Gc.WorkQueue.body_frame_log
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue
-- Complete builtin primitive-name lookup through a counted strcmp scan.
#print axioms OCaml.Vm.Boot.Startup.strcmp_frame_noise
#print axioms OCaml.Vm.Boot.Startup.NameComparePost.of_strcmp
#print axioms OCaml.Vm.Boot.Startup.compare_names
#print axioms OCaml.Vm.Boot.Startup.lookup_argument_input
#print axioms OCaml.Vm.Boot.Startup.lookup_branch_input
#print axioms OCaml.Vm.Boot.Startup.lookup_branch
#print axioms OCaml.Vm.Boot.Startup.lookup_compare
#print axioms OCaml.Vm.Boot.Startup.lookup_head
#print axioms OCaml.Vm.Boot.Startup.lookup_advance_input
#print axioms OCaml.Vm.Boot.Startup.lookup_advance
#print axioms OCaml.Vm.Boot.Startup.nextLookupIndex_nat
#print axioms OCaml.Vm.Boot.Startup.lookupIndex_nat
#print axioms OCaml.Vm.Boot.Startup.LookupAt.index_eq
#print axioms OCaml.Vm.Boot.Startup.lookup_iteration
#print axioms OCaml.Vm.Boot.Startup.lookup_loop
#print axioms OCaml.Vm.Boot.Startup.lookup_start_input
#print axioms OCaml.Vm.Boot.Startup.lookup_finish_input
#print axioms OCaml.Vm.Boot.Startup.lookup_run

#print axioms OCaml.Vm.Gc.WorkQueue.EnqueueSeparated.sourceOutsideRoot
#print axioms OCaml.Vm.Gc.pendingPayload_before
#print axioms OCaml.Vm.Gc.pendingPayload_enqueue
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_prefix_access
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_prefix_control
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_loadedNext
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_push_access
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_access
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_loadedFirst
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_machine
-- Source model initialization and runner setup, before architectural reset.
#print axioms OCaml.Vm.Boot.Startup.legalize_senvcfg_zero
#print axioms OCaml.Vm.Boot.Startup.legalize_mseccfg_zero
#print axioms OCaml.Vm.Boot.Startup.legalize_menvcfg_zero
#print axioms OCaml.Vm.Boot.Startup.model_init
#print axioms OCaml.Vm.Boot.Startup.register_tail_keeps_seed
#print axioms OCaml.Vm.Boot.Startup.initializer_keeps_seed
#print axioms OCaml.Vm.Boot.Startup.initializer_read_tail
#print axioms OCaml.Vm.Boot.Startup.initializer_model_seed
#print axioms OCaml.Vm.Boot.Startup.runner_defaults
#print axioms OCaml.Vm.Boot.Startup.runner_setup
#print axioms Vsa.Sim.RegisterWrites.lastValue_append
#print axioms Vsa.Sim.RegisterWrites.registers_read
#print axioms Vsa.Sim.RegisterWrites.apply_read
#print axioms Vsa.Sim.RegisterWrites.apply_read_append
#print axioms Vsa.Sim.RegisterWrites.registers_frame

#print axioms Vsa.Sim.memChain_low
#print axioms Vsa.Sim.evalBlocks_low
#print axioms OCaml.Vm.Gc.segmentPost_of_block
#print axioms OCaml.Vm.Gc.FieldCopy.head_access
#print axioms OCaml.Vm.Gc.FieldCopy.head_control
#print axioms OCaml.Vm.Gc.FieldCopy.store_access
#print axioms OCaml.Vm.Gc.FieldCopy.tail_access
#print axioms OCaml.Vm.Gc.FieldCopy.tail_control
#print axioms OCaml.Vm.Gc.FieldCopy.copy_access
#print axioms OCaml.Vm.Gc.FieldCopy.copy_machine
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.code
#print axioms OCaml.Vm.Gc.FieldCopy.header_unchanged
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.reflected
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.scan_regs
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.pc
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.memory

#print axioms OCaml.Vm.Gc.FieldCopy.header_nat
#print axioms OCaml.Vm.Gc.FieldCopy.header_window
#print axioms OCaml.Vm.Gc.FieldCopy.Geometry.write_window
#print axioms OCaml.Vm.Gc.FieldCopy.Geometry.windows
#print axioms OCaml.Vm.Gc.FieldCopy.word_frame
#print axioms OCaml.Vm.Gc.FieldCopy.immediate_tag
#print axioms OCaml.Vm.Gc.FieldCopy.again_eq
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAt.index_eq
#print axioms OCaml.Vm.Gc.FieldCopy.scan_iteration
#print axioms OCaml.Vm.Gc.FieldCopy.scan_loop
-- Checked configuration validation and architectural misa reset.
#print axioms OCaml.Vm.Boot.Startup.config_privs
#print axioms OCaml.Vm.Boot.Startup.config_tvecs
#print axioms OCaml.Vm.Boot.Startup.config_mstatus_fields
#print axioms OCaml.Vm.Boot.Startup.config_physaddr_bits
#print axioms OCaml.Vm.Boot.Startup.config_mmu_config
#print axioms OCaml.Vm.Boot.Startup.config_mmio_devices
#print axioms OCaml.Vm.Boot.Startup.config_vlen_elen
#print axioms OCaml.Vm.Boot.Startup.config_vext_config
#print axioms OCaml.Vm.Boot.Startup.config_pmp
#print axioms OCaml.Vm.Boot.Startup.config_misc_extension_dependencies
#print axioms OCaml.Vm.Boot.Startup.config_extension_param_constraints
#print axioms OCaml.Vm.Boot.Startup.config_version_constraints
#print axioms OCaml.Vm.Boot.Startup.config_stateen_config
#print axioms OCaml.Vm.Boot.Startup.resetPmas_valid
#print axioms OCaml.Vm.Boot.Startup.within_reset_pma
#print axioms OCaml.Vm.Boot.Startup.clint_window
#print axioms OCaml.Vm.Boot.Startup.signal_window
#print axioms OCaml.Vm.Boot.Startup.clint_address_bits
#print axioms OCaml.Vm.Boot.Startup.clint_size_bits
#print axioms OCaml.Vm.Boot.Startup.signal_address_bits
#print axioms OCaml.Vm.Boot.Startup.configMemoryProgram.eq
#print axioms OCaml.Vm.Boot.Startup.config_memory
#print axioms OCaml.Vm.Boot.Startup.config_valid_program
#print axioms OCaml.Vm.Boot.Startup.config_valid
#print axioms OCaml.Vm.Boot.Startup.reset_misa_run

#print axioms OCaml.Vm.Gc.FieldCopy.ScanAt.initial
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAt.payload
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAt.object
#print axioms OCaml.Vm.Gc.FieldCopy.pending_immediates
#print axioms OCaml.Vm.Gc.FieldCopy.scan_grey

#print axioms OCaml.Vm.Gc.FieldCopy.setup_access
#print axioms OCaml.Vm.Gc.FieldCopy.setup_machine
#print axioms OCaml.Vm.Gc.FieldCopy.setup_scan
-- Zero-state preservation through the architectural PMP reset loop.
#print axioms Vsa.Sim.Stays.pure
#print axioms Vsa.Sim.Stays.bind
#print axioms Vsa.Sim.Stays.forIn
#print axioms Vsa.Sim.Stays.unit
#print axioms Vsa.Sim.insert_present
#print axioms Vsa.Sim.writeReg_present
#print axioms OCaml.Vm.Boot.Startup.pmp_get
#print axioms OCaml.Vm.Boot.Startup.pmp_set
#print axioms OCaml.Vm.Boot.Startup.reset_pmp_run

#print axioms OCaml.Vm.Gc.mopupCode_after
#print axioms OCaml.Vm.Gc.WorkQueue.body_frame_words
#print axioms OCaml.Vm.Gc.WorkQueue.PopPost.word_unchanged
#print axioms OCaml.Vm.Gc.WorkQueue.PopPost.code
#print axioms OCaml.Vm.Gc.WorkQueue.PopPost.payload
#print axioms OCaml.Vm.Gc.WorkQueue.PopPost.setup_input
#print axioms OCaml.Vm.Gc.WorkQueue.View.scan_frame
#print axioms OCaml.Vm.Gc.WorkQueue.first_immediate
#print axioms OCaml.Vm.Gc.WorkQueue.PopPost.memory_frame
#print axioms OCaml.Vm.Gc.WorkQueue.pop_scan

#print axioms OCaml.Vm.Gc.WorkQueue.scan_after_pop
#print axioms OCaml.Vm.Gc.WorkQueue.resume_head_access
#print axioms OCaml.Vm.Gc.WorkQueue.resume_head_control
#print axioms OCaml.Vm.Gc.WorkQueue.resume_access
#print axioms OCaml.Vm.Gc.WorkQueue.resume_machine
#print axioms OCaml.Vm.Gc.WorkQueue.resume_scan
-- Complete source reset and the platform invariant of the ELF entry state.
#print axioms Vsa.Sim.state_eq
#print axioms Vsa.Sim.register_insert_frame
#print axioms OCaml.Vm.Boot.Startup.initializer_host
#print axioms OCaml.Vm.Boot.Startup.MisaResetPost.effect
#print axioms OCaml.Vm.Boot.Startup.reset_misa_effect
#print axioms OCaml.Vm.Boot.Startup.reset_tvecs_run
#print axioms OCaml.Vm.Boot.Startup.reset_sys_run
#print axioms OCaml.Vm.Boot.Startup.reset_run
#print axioms OCaml.Vm.Boot.Startup.init_model_run
#print axioms OCaml.Vm.Boot.Startup.setupElf_program
#print axioms OCaml.Vm.Boot.Startup.setupElf_run
#print axioms OCaml.Vm.Boot.Startup.elf_reset_exists
#print axioms OCaml.Vm.Boot.Startup.ElfReset.ready
#print axioms OCaml.Vm.Boot.Startup.whileMin_reset_exists

#print axioms OCaml.Vm.Gc.WorkQueue.empty_access
#print axioms OCaml.Vm.Gc.WorkQueue.empty_machine
#print axioms OCaml.Vm.Gc.WorkQueue.PopScanPost.empty_input
-- Startup image projections and execution from reset through C entry.
#print axioms OCaml.Vm.Boot.Startup.crt0_code
#print axioms OCaml.Vm.Boot.Startup.main_code
#print axioms OCaml.Vm.Boot.Startup.primitiveLookup_code
#print axioms OCaml.Vm.Boot.Startup.reset_image
#print axioms OCaml.Vm.Boot.Startup.reset_image_fillZero
#print axioms OCaml.Vm.Boot.Startup.reset_to_caml_main

#print axioms OCaml.Vm.Gc.Young.domain_window
#print axioms OCaml.Vm.Gc.Young.upper_access
#print axioms OCaml.Vm.Gc.Young.upper_control
#print axioms OCaml.Vm.Gc.Young.lower_access
#print axioms OCaml.Vm.Gc.Young.lower_control
#print axioms OCaml.Vm.Gc.Young.access
#print axioms OCaml.Vm.Gc.Young.decision
#print axioms OCaml.Vm.Gc.Young.classify
#print axioms OCaml.Vm.Gc.Young.decision_at_start
#print axioms OCaml.Vm.Gc.Young.decision_at_end
#print axioms OCaml.Vm.Gc.Young.nonpointer_outside
#print axioms OCaml.Vm.Gc.Young.Result.copy_nonpointer
-- Frozen ELF loader summarized by nonoverlapping byte-array pieces.
#print axioms Vsa.Sim.Boot.zip_push_both
#print axioms Vsa.Sim.Boot.array_push_induction
#print axioms Vsa.Sim.Boot.loadPiece_eq
#print axioms Vsa.Sim.Boot.initializeMemory_pieces
#print axioms Vsa.Sim.Boot.loadPieces_eq
#print axioms Vsa.Sim.Boot.initializeMemory_eq

#print axioms Vsa.Sim.gholds_select
#print axioms Vsa.Sim.gholds_of_frame
#print axioms OCaml.Vm.Gc.FieldCopy.head_access_bytes
#print axioms OCaml.Vm.Gc.FieldCopy.read_access
#print axioms OCaml.Vm.Gc.FieldCopy.read_machine
#print axioms OCaml.Vm.Gc.FieldCopy.ReadPost.young_input
#print axioms OCaml.Vm.Gc.FieldCopy.ReadPost.continuation
#print axioms OCaml.Vm.Gc.FieldCopy.classifier_continuation
#print axioms OCaml.Vm.Gc.FieldCopy.immediate_of_even
#print axioms OCaml.Vm.Gc.FieldCopy.classify_field
#print axioms OCaml.Vm.Gc.FieldCopy.ClassifiedPost.copy_nonpointer
-- Bounded byte views and the header of the exact archived while_min ELF.
#print axioms Vsa.Sim.Boot.bytesOfView_size
#print axioms Vsa.Sim.Boot.bytesOfView_get
#print axioms Vsa.Sim.Boot.bytesOfView_extract
#print axioms Vsa.Sim.Boot.nbytes_ext
#print axioms Vsa.Sim.Boot.elfHeader_prefix
#print axioms Vsa.Sim.Boot.elfHeader_view
#print axioms Vsa.Sim.Boot.elfHeader_parse_view
#print axioms OCaml.Vm.Boot.WhileMinElfParse.source_header
#print axioms OCaml.Vm.Boot.WhileMinElfParse.header_eq
#print axioms OCaml.Vm.Boot.WhileMinElfParse.source_header_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.header_entry

#print axioms OCaml.Vm.Gc.FieldCopy.store_tail_access
#print axioms OCaml.Vm.Gc.FieldCopy.store_machine
#print axioms OCaml.Vm.Gc.FieldCopy.ClassifiedPost.store_input
#print axioms OCaml.Vm.Gc.FieldCopy.CopyPost.effect
#print axioms OCaml.Vm.Gc.FieldCopy.StorePost.effect
#print axioms OCaml.Vm.Gc.FieldCopy.copy_even
-- Bounded ELF table-entry locality and the two concrete table parsers.
#print axioms Vsa.Sim.Boot.parser_view_of_slice
#print axioms Vsa.Sim.Boot.elfProgramHeader_slice
#print axioms Vsa.Sim.Boot.elfProgramHeader_parse_slice
#print axioms Vsa.Sim.Boot.elfProgramHeader_parse_view
#print axioms Vsa.Sim.Boot.elfSectionHeader_slice
#print axioms Vsa.Sim.Boot.elfSectionHeader_parse_slice
#print axioms Vsa.Sim.Boot.elfSectionHeader_parse_view
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program0_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program1_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program2_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program3_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section0_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section1_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section2_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section3_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section4_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section5_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section6_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section7_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section8_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section9_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section10_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section11_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section12_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program_table_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section_table_parse

#print axioms OCaml.Vm.Gc.FieldCopy.CopyEffect.mono
#print axioms OCaml.Vm.Gc.FieldCopy.even_of_immediate_false
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.index_eq
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.advance
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.loop
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.initial
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.payload
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.object
#print axioms OCaml.Vm.Gc.FieldCopy.DomainFrame.at
#print axioms OCaml.Vm.Gc.FieldCopy.mixed_iteration
#print axioms OCaml.Vm.Gc.FieldCopy.mixed_scan
#print axioms OCaml.Vm.Gc.FieldCopy.pending_nonYoung
#print axioms OCaml.Vm.Gc.FieldCopy.scan_mixed_grey

#print axioms OCaml.Vm.Gc.image_after
#print axioms OCaml.Vm.Gc.oldifyCode_after
#print axioms OCaml.Vm.Gc.Forwarded.access
#print axioms OCaml.Vm.Gc.Forwarded.forwarded_machine
#print axioms OCaml.Vm.Gc.Forwarded.Post.slot_relocates
#print axioms OCaml.Vm.Gc.Forwarded.Post.target_from_links
#print axioms OCaml.Vm.Gc.Forwarded.Post.queue_frame

#print axioms OCaml.Vm.Gc.OldifyReturn.return_machine
#print axioms OCaml.Vm.Gc.OldifyReturn.SavedSame.returnWord
#print axioms OCaml.Vm.Gc.OldifyReturn.SavedSame.restored
#print axioms OCaml.Vm.Gc.Forwarded.Post.saved_same
#print axioms OCaml.Vm.Gc.Forwarded.Post.return_input
#print axioms OCaml.Vm.Gc.Forwarded.forwarded_return
-- Actual ELF interpretation, complete parser, and startup metadata.
#print axioms Vsa.Sim.Boot.mapM_ok
#print axioms Vsa.Sim.Boot.segment_view
#print axioms Vsa.Sim.Boot.segments_view
#print axioms Vsa.Sim.Boot.sectionNames_view
#print axioms Vsa.Sim.Boot.section_view
#print axioms Vsa.Sim.Boot.sections_view
#print axioms Vsa.Sim.Boot.elf64File_parse
#print axioms Vsa.Sim.Boot.rawElf64_parse
#print axioms Vsa.Sim.Boot.rawElf64_view
#print axioms Vsa.Sim.Boot.rangeViews
#print axioms OCaml.Vm.Boot.WhileMinElfSort.ranges_sorted
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ranges_sorted
#print axioms OCaml.Vm.Boot.WhileMinElfParse.program_bounds
#print axioms OCaml.Vm.Boot.WhileMinElfParse.section_bounds
#print axioms OCaml.Vm.Boot.WhileMinElfParse.segments_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.names_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.interpreted_sections_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.gaps_geometry
#print axioms OCaml.Vm.Boot.WhileMinElfParse.gaps_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.file_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.raw_file_parse
#print axioms OCaml.Vm.Boot.WhileMinElfParse.entry_metadata
#print axioms OCaml.Vm.Boot.WhileMinElfParse.tohost_metadata

#print axioms OCaml.Vm.Gc.OldifyReturn.SavedSame.of_writeLog
#print axioms OCaml.Vm.Gc.WorkQueue.View.memory_eq
#print axioms OCaml.Vm.Gc.WorkQueue.EnqueuePost.memory_eq
#print axioms OCaml.Vm.Gc.WorkQueue.EnqueueRunPost.memory_effect
#print axioms OCaml.Vm.Gc.WorkQueue.EnqueueRunPost.code
#print axioms OCaml.Vm.Gc.WorkQueue.EnqueueRunPost.return_input
#print axioms OCaml.Vm.Gc.WorkQueue.enqueue_return
-- Closed parsed-image loader and reset-to-caml_main witness.
#print axioms Vsa.Sim.Boot.loaderViews_ok
#print axioms Vsa.Sim.Boot.loaderViews_shape
#print axioms Vsa.Sim.Boot.foldRanges_nonempty
#print axioms Vsa.Sim.Boot.initializeMemory_views
#print axioms OCaml.Vm.Boot.WhileMinElfData.loader_separate
#print axioms OCaml.Vm.Boot.WhileMinElfData.loader_bytes
#print axioms OCaml.Vm.Boot.WhileMinElfParse.pieces_view
#print axioms OCaml.Vm.Boot.WhileMinElfParse.pieces_ok
#print axioms OCaml.Vm.Boot.WhileMinElfParse.loaded_memory
#print axioms OCaml.Vm.Boot.WhileMinElfParse.whileMin_elf
#print axioms OCaml.Vm.Boot.WhileMinElfParse.reset_exists
#print axioms OCaml.Vm.Boot.WhileMinElfParse.reset_caml_main_exists

#print axioms Vsa.Sim.tr_appterm1
#print axioms OCaml.Vm.Sim.appterm1_loaded
#print axioms Vsa.Sim.tr_appterm2
#print axioms OCaml.Vm.Sim.appterm2_loaded
#print axioms Vsa.Sim.tr_appterm3
#print axioms OCaml.Vm.Sim.appterm3_loaded
#print axioms OCaml.Vm.Sim.value_entries_distinct
#print axioms OCaml.Vm.Sim.value_entries_selected
#print axioms OCaml.Vm.Sim.value_log_in
#print axioms OCaml.Vm.Sim.value_log_words
#print axioms OCaml.Vm.Sim.payload_copy_prefix
#print axioms OCaml.Vm.Sim.tailcall_restore
#print axioms OCaml.Vm.Sim.tailcall_offset
#print axioms OCaml.Vm.Sim.tailcall_address
#print axioms OCaml.Vm.Sim.tailcall_extra
#print axioms OCaml.Vm.Sim.appterm1_arm
#print axioms OCaml.Vm.Sim.appterm1_step_arm
#print axioms OCaml.Vm.Sim.appterm2_arm
#print axioms OCaml.Vm.Sim.appterm2_step_arm
#print axioms OCaml.Vm.Sim.appterm3_arm
#print axioms OCaml.Vm.Sim.appterm3_step_arm

#print axioms OCaml.Vm.Gc.outLRange_of_forall
#print axioms OCaml.Vm.Gc.word_writeLog_cells
#print axioms OCaml.Vm.Gc.stack_bound
#print axioms OCaml.Vm.Gc.stack_address
#print axioms OCaml.Vm.Gc.OldifyEntry.head_control
#print axioms OCaml.Vm.Gc.OldifyEntry.access
#print axioms OCaml.Vm.Gc.OldifyEntry.entry_machine
#print axioms OCaml.Vm.Gc.OldifyEntry.Input.frame_bound
#print axioms OCaml.Vm.Gc.OldifyEntry.saved_address
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.saved
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.restored_caller
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.returnWord
-- Startup allocation dispatch and abstract BSS readback.
#print axioms OCaml.Vm.Boot.Startup.statAlloc_code
#print axioms OCaml.Vm.Boot.Startup.statAlloc_input
#print axioms OCaml.Vm.Boot.Startup.statAlloc_dispatch
#print axioms OCaml.Vm.Boot.Startup.statAlloc_with_malloc
#print axioms OCaml.Vm.Boot.Startup.zeroWord_byte
#print axioms OCaml.Vm.Boot.Startup.clearWords_inside
#print axioms OCaml.Vm.Boot.Startup.clearWords_pins
#print axioms OCaml.Vm.Boot.Startup.clearWords_log_pins
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.bss_pins
#print axioms OCaml.Vm.Boot.Startup.mainWrites_between
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.pool_zero
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.domain_zero
#print axioms OCaml.Vm.Boot.Startup.call_8000ab48
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab2cTRow
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab2cFRow
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab38Row
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab4cTRow
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab4cFRow
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab50Row
#print axioms Vsa.Sim.caml_stat_alloc_noexcXab7cRow

#print axioms OCaml.Vm.Gc.OldifyYoung.upper_access
#print axioms OCaml.Vm.Gc.OldifyYoung.lower_access
#print axioms OCaml.Vm.Gc.OldifyYoung.upper_control
#print axioms OCaml.Vm.Gc.OldifyYoung.lower_control
#print axioms OCaml.Vm.Gc.OldifyYoung.access
#print axioms OCaml.Vm.Gc.OldifyYoung.young_machine
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.word_unchanged
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.young_input
#print axioms OCaml.Vm.Gc.OldifyEntry.Input.return_windows
#print axioms OCaml.Vm.Gc.OldifyEntry.Post.carried
#print axioms OCaml.Vm.Gc.OldifyEntry.carried_after_young
#print axioms OCaml.Vm.Gc.ForwardedCall.after_entry
#print axioms OCaml.Vm.Gc.ForwardedCall.forwarded_call

#print axioms OCaml.Vm.Gc.image_writeLog
#print axioms OCaml.Vm.Gc.ForwardedCall.Input.effect_high
#print axioms OCaml.Vm.Gc.ForwardedCall.Post.mopupCode
#print axioms OCaml.Vm.Gc.MopupCall.carried_regs
#print axioms OCaml.Vm.Gc.MopupCall.linked_regs
#print axioms OCaml.Vm.Gc.MopupCall.linked_input
#print axioms OCaml.Vm.Gc.MopupCall.forwarded
#print axioms OCaml.Vm.Gc.MopupCall.resume_forwarded
#print axioms OCaml.Vm.Gc.MopupCall.forwarded_resume
-- RESTART forward-copy loop: generated iterations and counted closure-field snapshot.
#print axioms OCaml.Vm.Sim.forward_copy_log_step
#print axioms OCaml.Vm.Sim.forward_copy_log_complete
#print axioms OCaml.Vm.Sim.outLRange_subrange
#print axioms OCaml.Vm.Sim.forward_copy_source_outside
#print axioms OCaml.Vm.Sim.forward_counter_step
#print axioms OCaml.Vm.Sim.forward_source_address
#print axioms OCaml.Vm.Sim.forward_cursor_step
#print axioms OCaml.Vm.Sim.forward_store_address
#print axioms OCaml.Vm.Sim.forward_copy_guard
#print axioms OCaml.Vm.Sim.ForwardCopyAt.index
#print axioms OCaml.Vm.Sim.ForwardCopyAt.read
#print axioms OCaml.Vm.Sim.ForwardCopyAt.advance
#print axioms OCaml.Vm.Sim.ForwardCopyRegion.entry
#print axioms OCaml.Vm.Sim.forward_copy_loop
#print axioms OCaml.Vm.Sim.forward_copy_more
#print axioms OCaml.Vm.Sim.forward_copy_last
#print axioms OCaml.Vm.Sim.forward_copy_iteration
#print axioms OCaml.Vm.Sim.forward_copy_run


-- Complete represented RESTART through its concrete generated loop.
#print axioms OCaml.Vm.Sim.StackEditOutside.root_field_load
#print axioms OCaml.Vm.Sim.StackEditOutside.env_field_load
#print axioms OCaml.Vm.Sim.restart_count_word
#print axioms OCaml.Vm.Sim.restart_stack_word
#print axioms OCaml.Vm.Sim.restart_empty_guard
#print axioms OCaml.Vm.Sim.RestartInput.copy_region
#print axioms OCaml.Vm.Sim.RestartInput.copy_after
#print axioms OCaml.Vm.Sim.restart_setup_more
#print axioms OCaml.Vm.Sim.restart_setup_empty
#print axioms OCaml.Vm.Sim.restart_finish
#print axioms OCaml.Vm.Sim.restart_arm
#print axioms OCaml.Vm.Sim.restart_step_arm


-- GRAB allocation cuts and shared represented block restoration.
#print axioms Vsa.Sim.tr_grab_alloc_prefix
#print axioms OCaml.Vm.Sim.grab_alloc_prefix_loaded
#print axioms Vsa.Sim.tr_grab_alloc_init
#print axioms OCaml.Vm.Sim.grab_alloc_init_loaded
#print axioms Vsa.Sim.tr_grab_copy_more
#print axioms OCaml.Vm.Sim.grab_copy_more_loaded
#print axioms Vsa.Sim.tr_grab_copy_last
#print axioms OCaml.Vm.Sim.grab_copy_last_loaded
#print axioms Vsa.Sim.tr_grab_alloc_suffix
#print axioms OCaml.Vm.Sim.grab_alloc_suffix_loaded
#print axioms OCaml.Vm.Sim.block_header_ok
#print axioms OCaml.Vm.Sim.block_layout_of_words
#print axioms OCaml.Vm.Sim.block_log_layout
#print axioms OCaml.Vm.Sim.block_allocation_roots
#print axioms OCaml.Vm.Sim.grab_allocation_roots
#print axioms OCaml.Vm.Sim.grab_restore


-- Shared counted-loop fold and the actual GRAB source-cursor loop.
#print axioms OCaml.Run.counted_loop
#print axioms OCaml.Vm.Sim.forward_copy_load
#print axioms OCaml.Vm.Sim.copy_store_entry
#print axioms OCaml.Vm.Sim.forward_copy_memory_step
#print axioms OCaml.Vm.Sim.CursorCopyAt.index
#print axioms OCaml.Vm.Sim.CursorCopyAt.read
#print axioms OCaml.Vm.Sim.cursor_copy_guard
#print axioms OCaml.Vm.Sim.CursorCopyAt.advance
#print axioms OCaml.Vm.Sim.cursor_copy_loop
#print axioms OCaml.Vm.Sim.cursor_copy_more
#print axioms OCaml.Vm.Sim.cursor_copy_last
#print axioms OCaml.Vm.Sim.cursor_copy_iteration
#print axioms OCaml.Vm.Sim.cursor_copy_run


-- Partial-closure layout and concrete G1 GRAB reservation.
#print axioms OCaml.Vm.Sim.value_log_framed
#print axioms OCaml.Vm.Sim.outLRange_append
#print axioms OCaml.Vm.Sim.partial_closure_layout
#print axioms OCaml.Vm.Sim.RamWriteAt.read
#print axioms OCaml.Vm.Sim.grab_alloc_guard
#print axioms OCaml.Vm.Sim.grab_size_word
#print axioms OCaml.Vm.Sim.grab_reservation_word
#print axioms OCaml.Vm.Sim.grab_alloc_prefix_domain
#print axioms OCaml.Vm.Sim.grab_alloc_init_domain
#print axioms OCaml.Vm.Sim.grab_reserve


-- GRAB initializer establishes its concrete counted-copy input.
#print axioms OCaml.Vm.Sim.GrabInitInput.copy_after
#print axioms OCaml.Vm.Sim.grab_copy_nonempty
#print axioms OCaml.Vm.Sim.grab_source_end
#print axioms OCaml.Vm.Sim.grab_initialize

-- Startup frame, first runtime calls, and allocator bootstrap obligation.
#print axioms Vsa.Sim.Boot.loaderMem_bytes
#print axioms Vsa.Sim.Boot.bytesT_local_eq
#print axioms OCaml.Vm.Boot.Startup.mainWrites_before
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.memory_below
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.bytes_below
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.image
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.leaf
#print axioms OCaml.Vm.Boot.Startup.heap_base_word
#print axioms OCaml.Vm.Boot.Startup.initial_sbrk_base
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.sbrk_base
#print axioms OCaml.Vm.Boot.Startup.heap_not_initialized
#print axioms OCaml.Vm.Boot.Startup.prefix_call_post
#print axioms OCaml.Vm.Boot.Startup.caml_main_prefix_input
#print axioms OCaml.Vm.Boot.Startup.caml_main_prefix_log
#print axioms OCaml.Vm.Boot.Startup.caml_main_prefix
#print axioms OCaml.Vm.Boot.Startup.caml_main_domain
#print axioms OCaml.Vm.Boot.Startup.domain_prefix_input
#print axioms OCaml.Vm.Boot.Startup.domain_prefix_log
#print axioms OCaml.Vm.Boot.Startup.domain_prefix
#print axioms OCaml.Vm.Boot.Startup.domain_allocate
#print axioms OCaml.Vm.Boot.Startup.call_80004d94
#print axioms OCaml.Vm.Boot.Startup.call_8002a8e8
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetCamlMainWitness.sbrk_base
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetCamlMainWitness.heap_not_initialized

#print axioms Vsa.Sim.lookupG_eraseG_ne
#print axioms Vsa.Sim.srcVal_eraseG_ne
#print axioms Vsa.Sim.gholds_key_eq
#print axioms Vsa.Sim.regGet_of_gprGet_eq
#print axioms Vsa.Sim.frame_of_restored
#print axioms OCaml.Vm.Gc.FieldCopy.tail_access_bytes
#print axioms OCaml.Vm.Gc.FieldCopy.advance_access
#print axioms OCaml.Vm.Gc.FieldCopy.advance_machine
#print axioms OCaml.Vm.Gc.MopupCall.preserved_pins
#print axioms OCaml.Vm.Gc.MopupCall.abi_frame
#print axioms OCaml.Vm.Gc.MopupCall.ResumedPost.advance_input
#print axioms OCaml.Vm.Gc.MopupCall.forwarded_advance
-- Closed actual-reset execution through the first malloc entry.
#print axioms OCaml.Vm.Primitives.BlockPost.frame_subset
#print axioms OCaml.Vm.Primitives.lpins8_writeLog
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetCamlMainWitness.savedReg
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetCamlMainWitness.prefixInput
#print axioms OCaml.Vm.Boot.WhileMinElfParse.reset_domain_exists
#print axioms OCaml.Vm.Boot.WhileMinElfParse.camlMainLog_below
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetDomainWitness.prefixInput
#print axioms OCaml.Vm.Boot.WhileMinElfParse.reset_stat_alloc_exists
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetStatAllocWitness.pool_zero
#print axioms OCaml.Vm.Boot.WhileMinElfParse.reset_malloc_exists

#print axioms OCaml.Vm.Gc.ForwardedCall.Conditions.memory_eq
#print axioms OCaml.Vm.Gc.ForwardedField.Input.read_input
#print axioms OCaml.Vm.Gc.ForwardedField.Input.carried
#print axioms OCaml.Vm.Gc.ForwardedField.classifier_carried
#print axioms OCaml.Vm.Gc.ForwardedField.classifier_input
#print axioms OCaml.Vm.Gc.ForwardedField.forwarded_field

#print axioms OCaml.Vm.Gc.MopupCall.AdvancedPost.word_frame
#print axioms OCaml.Vm.Gc.MopupCall.againAfterCall_frame
#print axioms OCaml.Vm.Gc.MopupCall.AdvancedPost.slot_relocates
#print axioms OCaml.Vm.Gc.MopupCall.againAfterCall_count
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.advance_progress
#print axioms OCaml.Vm.Gc.MopupCall.AdvancedPost.progress

#print axioms OCaml.Vm.Gc.logInW_of_forall
#print axioms OCaml.Vm.Gc.MopupCall.effect_entry
#print axioms OCaml.Vm.Gc.MopupCall.scanFootprint_of_geometry
#print axioms OCaml.Vm.Gc.ForwardedField.scan_iteration

#print axioms OCaml.Vm.Gc.outW_of_range
#print axioms OCaml.Vm.Gc.frame_word
#print axioms OCaml.Vm.Gc.ForwardedCall.effect_high
#print axioms OCaml.Vm.Gc.ForwardedCall.Conditions.frame
#print axioms OCaml.Vm.Gc.ForwardedField.Input.oldifyCode_after
#print axioms OCaml.Vm.Gc.ForwardedField.Input.stable
#print axioms OCaml.Vm.Gc.ForwardedField.stable_after
#print axioms OCaml.Vm.Gc.ForwardedField.Input.next_registers
-- Initial allocator metadata and its first morecore branch.
#print axioms OCaml.Vm.Boot.Startup.sbrk_r_boot
#print axioms OCaml.Vm.Boot.Startup.readLE_exists_of_present
#print axioms OCaml.Vm.Boot.Startup.read64_of_word
#print axioms OCaml.Vm.Boot.Startup.clearWords_present
#print axioms OCaml.Vm.Boot.Startup.CrtCamlMainPost.present
#print axioms OCaml.Vm.Boot.Startup.initial_top
#print axioms OCaml.Vm.Boot.Startup.initial_binblocks
#print axioms OCaml.Vm.Boot.Startup.initial_bin_links
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.read_frame
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.main_present
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.present
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.initial_read
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.bss_read
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.empty_bins
#print axioms OCaml.Vm.Boot.WhileMinElfParse.ResetMallocWitness.initial_arena

#print axioms Vsa.Sim.indexedLoop
#print axioms OCaml.Vm.Gc.ForwardedField.Input.scan_progress
#print axioms OCaml.Vm.Gc.ForwardedField.cursor_next
#print axioms OCaml.Vm.Gc.ForwardedField.LoopAt.source
#print axioms OCaml.Vm.Gc.ForwardedField.LoopAt.input
#print axioms OCaml.Vm.Gc.ForwardedField.LoopAt.step
#print axioms OCaml.Vm.Gc.ForwardedField.forwarded_scan

#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.relocated_payload
#print axioms OCaml.Vm.Gc.FieldCopy.ScanAtWith.relocated_object
#print axioms OCaml.Vm.Gc.ForwardedField.scan_relocated
#print axioms OCaml.Vm.Gc.ForwardedField.LoopAt.initial
#print axioms OCaml.Vm.Boot.Startup.InitialArena.bin_links
#print axioms OCaml.Vm.Boot.Startup.malloc_boot_prefix

#print axioms OCaml.Vm.Gc.OldifyBridge.carried_regs
#print axioms OCaml.Vm.Gc.OldifyBridge.linked_regs
#print axioms OCaml.Vm.Gc.OldifyBridge.linked_input
#print axioms OCaml.Vm.Gc.OldifyBridge.forwarded
#print axioms OCaml.Vm.Gc.OldifyBridge.preserved_pins
#print axioms OCaml.Vm.Gc.OldifyBridge.abi_frame
#print axioms OCaml.Vm.Gc.OldifyBridge.resume_forwarded
#print axioms OCaml.Vm.Gc.OldifyBridge.forwarded_resume
#print axioms OCaml.Vm.Gc.FirstCall.forwarded
#print axioms OCaml.Vm.Gc.FirstCall.forwarded_resume

#print axioms OCaml.Vm.Gc.ChainAccess.retarget
#print axioms OCaml.Vm.Gc.Young.classify_site
#print axioms OCaml.Vm.Gc.FirstYoung.access
#print axioms OCaml.Vm.Gc.FirstYoung.classify
#print axioms OCaml.Vm.Boot.Startup.malloc_boot_morecore
#print axioms OCaml.Vm.Boot.Startup.malloc_boot_alignment
#print axioms OCaml.Vm.Boot.Startup.MallocBootAtCall.sbrk_pre
#print axioms OCaml.Vm.Boot.Startup.MFrame.after_sbrk
