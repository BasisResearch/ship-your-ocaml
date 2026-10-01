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
#print axioms OCaml.Vm.Sim.isint_loaded
#print axioms Vsa.Sim.tr_const0
#print axioms OCaml.Vm.Sim.const0_loaded
#print axioms Vsa.Sim.site_800035c0_const0
#print axioms Vsa.Sim.site_800035c4_const0
#print axioms Vsa.Sim.site_800035c8_const0
/-! Generated smoke sites for the 16 extended ALU classes. -/
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
