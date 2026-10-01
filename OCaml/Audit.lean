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
#print axioms Vsa.Sim.tr_offsetint
#print axioms OCaml.Vm.Sim.offsetint_loaded
#print axioms OCaml.Vm.Sim.offsetintOperand_large
#print axioms OCaml.Vm.Sim.offsetint_width_obstruction
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
