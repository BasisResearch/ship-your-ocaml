# Phases

The goal is `endToEnd_ocaml` (`OCaml/EndToEnd.lean`): the bytes of
`boot/ocamlc`, compiling a program `src`, produce an executable that the
bare-metal `ocamlrun` runs with exactly `OCamlSem`'s behaviours of `src`.
It is PROVED from three obligations; this file is their ledger and the
phase plan. PLAN.md explains the layers.

```
OCamlSem p  ↔  BcSem (ocamlc p)  ↔  Halts c out e
     Layer C                 Layer A
BcSem boot/ocamlc  ↔  OCamlSem ocamlc-src   (fixpoint + Layer C on the compiler's build)
Layer B′: the program logic over BcSem that makes compiler-sized bytecode proofs feasible
```

No statement below is an axiom or a `sorry`: open statements are `Prop`s
(`OCaml/Theorems.lean`), obligations are structures. `scripts/check_all.sh`
gates the tree (build, no holes, axiom audit, discipline, generator drift,
ELF pin).

## Ledger

| statement / obligation | file | phase | status |
|---|---|---|---|
| `halts_or_diverges`, `BcHalts.det`, `BcHalts.not_diverges` | `OCaml/Bytecode/Semantics.lean` | P0 | **proved** |
| `ledger_exact`, `ledger_fragment`, `f1_count`, `primF1_unsupported` | `OCaml/Fragment.lean` | P0 | **proved** (`decide`) |
| `bcHalts_of_runTo` (checked runs are behaviours) | `OCaml/Bytecode/Load.lean` | P0 | **proved** |
| `whileMin_bcSem : BcHalts whileMin "55\n2500\n36\n" 0` | `OCaml/Programs/Validation.lean` | P0 | **proved** (kernel `decide`) |
| `ocamlrun_refinement_of_sim`, `ocamlrun_refinement_fillZero` | `OCaml/Refinement.lean` | P0 | **proved** |
| `simOfArms`, `ocamlrun_refinement_of_arms` (Layer A from per-arm obligations) | `OCaml/Refinement.lean` | P0 | **proved** |
| `bytecode_logic_adequacy` (Layer B′ adequacy) | `OCaml/Logic/BcModel.lean`, `OCaml/Theorems.lean` | P0 | **proved** (instance of `VsaIris.mach_adequacy`) |
| `boot_meaning`, `endToEnd_ocaml` / `endToEnd_of_layers` (composition) | `OCaml/EndToEnd.lean`, `OCaml/Theorems.lean` | P0 | **proved** |
| run kernel: run laws of every step relation (`iter`, presentations, lossy transport); R1–R3 re-proved through it | `OCaml/Run/`, `Semantics.lean`, `Refinement.lean`, `BcModel.lean` | round 1 | **proved** (adopted, `abstractions/ROUND-1.md`) |
| `halts_iff_bcHalts`, `ocamlrun_refinement_exit`, `ocamlrun_refinement_bcModel` | `OCaml/Logic/BcModel.lean`, `OCaml/Theorems.lean` | round 1b | **proved** |
| relocation invariance of all `VmReprAt` fields (`Eqv` combinators) | `OCaml/Vm/Reloc.lean` | round 1 (A6 route) | **proved** under the typed relocation; the real-collector bridge `ScanCoherent` is open (A6) |
| symbolic stepping + `loop_rule`; a counting loop for any bound | `OCaml/Logic/Symbolic.lean`, `OCaml/Programs/CountLoop.lean` | round 1 (B′ route) | **proved** |
| OS spec (SibylFS + CakeML port), executable checker `allowed_sound`/`allowed_complete`/`checkTrace_sound` | `tcb/TCB/Os/` | P0 | **proved**; spec **trusted** for Linux, validated on 6,490 Linux traces (0 rejected) |
| library proofs of the 66 byte-identical functions retargeted to this ELF | `Vsa/`, `scripts/retarget_syi.py` | P0 | **done** (pins checked, `memcpy_bytepath_spec`/`muldi3_spec`/`udivdi3_spec` audited) |
| `strcmp_full_spec_cond` for this ELF (aligned and unaligned ASCII C strings, framed return) | `Vsa/Sim/StrcmpSpecCond.lean` | A0 | **proved**, regenerated address/mask retarget, pinned and audited |
| `ssputs_fast_spec` and `ssprint_iov2_spec` for this ELF (short disjoint copies, sufficient capacity, two iovecs) | `Vsa/Sim/SnprintfSpec19.lean`, `SnprintfSpec20Part4.lean` | A0 | **proved**, retargeted call/region addresses, pinned and audited; framed return and copied bytes |
| Allocator symbolic-run soundness and regenerated instruction table | `VsaIris/Vsa/SymRun.lean`, `AllocSteps/Part*.lean` | A0 | **proved**: 1,459 instruction-step lemmas, including all `_malloc_r` and `_free_r` words; generic SWP soundness and representative entry sites audited; a5 drift check |
| Allocator heap geometry, sbrk and checked malloc paths | `VsaIris/Vsa/{HeapTake,HeapFree,MallocPaths,MallocExtend}.lean` | A0 | **proved**: relocated bin/global geometry, split/coalesce/frame preservation, `_sbrk_r`, small/remainder/top/growth paths; 45-module generated closure, headline audits and a5 drift check |
| `_malloc_r` and `malloc` function contracts for this ELF | `VsaIris/Vsa/MallocBlocks2.lean`, `MallocRunAll.lean` | A0 | **proved**: `malloc_all` at `_malloc_r` entry, plus `mallocChgRun_proved` and `mallocLocalRun_proved`; complete generated step/pin closure, audited |
| `_free_r` and `free` function contracts for this ELF | `VsaIris/Vsa/FreeTop.lean`, `FreeRunAll.lean` | A0 | **proved**: `free_body` at `_free_r` entry, plus `freeChgRun_proved` and `freeLocalRun_proved`; coalescing, trimming and complete generated step/pin closure, audited |
| `_svfprintf_r` function spec for this ELF | `VsaIris/Vsa/SnpFmt.lean` | A0 | **proved**: `svfprintf_nw` at `0x8004789c`, entry-to-return for literal text, `%s`, and `%d`; initialized string FILE, ASCII locale, bounded stack arguments/output, truncated bytes and full rendered-length return; 47 generated modules, pinned and audited, a5 drift check |
| decode for every disassembled instruction word (via syi’s `decodeW`) | `Vsa/Sim/ElfDecode/`, `scripts/gen_elf_decode.py` | A0 | **proved**: 29,473 words, 231 chunks; covers all reachable words; a5 drift check |
| `HtifFsImplements` (the in-image file system meets the OS spec) | `OCaml/Os.lean` | F5 | reduced by `htifFsImplements_of_functions` to `HtifEntries` + `HtifFunctionObligations` (termination/partial correctness); premises open. Concrete classifier and candidate memory relation in `OCaml/Os/HtifMemory.lean`; ABI decoding remains open. Original corpus: 6,410 accepted, 80 special (`results/htif-fs.json`). Additional 256-byte-name trace is rejected; kernel-checked spec obstruction in `DirectoryObstruction.lean`, runtime repair required |
| `BcSem` world over `TCB.Os.OsState` (file/time/env primitives through `OsStep`) | `OCaml/Bytecode/Semantics.lean` | F5 | **implemented and differential-tested**; includes directory streams, channel Marshal and MD5; selected calls inherit `osCall_sound` |
| Linux instantiation: `ecall` as an external step constrained by `OsStep` | `Vsa.Machine` extension | E | open |
| `Layout.runtimeOk` concrete instance | `OCaml/Vm/Runtime.lean` | A0 | **defined**: `runtimeLayout freeList`, with ordinary nonempty-nursery bounds |
| `Loaded` at real entry states (boot witnesses, small programs) | `OCaml/Vm/Boot/` | A0 | **proved for the complete captured while_min cut**: `WhileMin.loaded_fillZero`, no premises; full native-state comparison; kernel reset-to-cut execution remains open |
| Reset-to-cut startup execution, then `Loaded` | `OCaml/Vm/Boot/Startup/` | A0 Round 2 | **open**: function-summary composition from the pinned image reset state; `reset_to_caml_main` now composes the actual reset platform with generated executable-image projections and crt0/main, including exact main writes and embedded argv preservation (closed actual-ELF supplier `WhileMinElfParse.whileMin_elf` and `reset_caml_main_exists` proved); reset metadata/entry PC and `runner_setup` (model initialization plus complete register initialization) proved; complete `setupElf_run` and `elf_reset_exists` proved, including configuration validation, all architectural reset stages, `GoodState`, entry PC and loader-memory preservation; generic `initializeMemory_eq` loader correspondence proved by disjoint piece folds, exact pinned-file raw ELF parser, segment/section interpretation, file-gap geometry and entry/HTIF metadata proved by bounded-view locality; concrete loader-byte correspondence proved by symbolic range aliases; closed `WhileMinElfParse.reset_malloc_exists` reaches the first malloc entry with a 928-byte request from actual reset; **`reset_first_allocation_exists` now extends that execution through the complete first malloc return**, with exact first pointer, restored ABI and initialized heap shape, via `symbolic_summary`; **`reset_minor_tables_exists` reaches `caml_alloc_minor_tables`**, after source publication of `Caml_state` and thirteen domain-field zero stores, with exact generated write log and restored executable-image interface; `ResetMinorTables.room/vsaOk/readOnly` supply remaining allocation credits and complete library inputs at that call, and `allocator_summary` bridges the landed successful allocator contract for arbitrary later requests; `reset_table_alloc_exists` closes reset reachability to the first 56-byte minor-table allocation request, with normalized generated code/access certificates and exact stack saves; **`reset_table_allocation_exists` now reaches the successful first table malloc return**, with fresh aligned block and remaining credits; `memset56_prefix` and generic `zero_pairs` now summarize the aligned entry and native word-pair loop with exact zero-store effects; `memset56` now composes the eight-byte tail and return, with `memset56Memory_inside/out` proving complete zeroing and the allocation frame; **`reset_table_zeroed_exists` now reaches return from the first table memset**, after actual publication and reload; generic publication covers all three Layout table fields, and both ordinary memset call sites are composed; `ResetTableZeroed.ready` now carries complete platform, read-only pins, capacity, stack, domain and disabled-pooling facts into the next allocation; **`reset_second_allocation_exists` now reaches the second table malloc return**, with generic summaries for both remaining allocation sites and their publication inputs; **`reset_third_allocation_exists` now reaches the third table malloc return**, after generic second-table publication/zeroing and readiness preservation; **`reset_tables_return_exists` now completes all three minor-table allocations/publications/zeroings and restores the source caller frame**, returning to caml_init_domain; **`reset_domain_returned_exists` now completes the remaining 35 domain stores and returns to caml_main**, restoring its original saved link from before the first malloc; `ResetDomainReturned.ready` retains full platform/read-only/capacity/global facts at that return via frame-independent `RuntimeReady`; shared `identity_zero`/`identity_call` summaries now supply the four bare-metal user/group security checks; `secure_getenv_to_getenv` now composes the complete successful security wrapper through its getenv tail call, with generic native-frame and runtime-state preservation; `reset_parameter_entry_exists` now reaches the parameter-parser entry from actual reset with retained runtime state and packed execution history; both environment lock wrappers and their no-op recursive hooks are summarized; `name_scan` folds the native environment-name scan with a shared indexed-loop rule and full register/memory frame; `name_scan_empty` reaches the not-found branch for an empty environment, and `find_tail` composes the unlock and complete restoring null return; `find_locked` covers the saving prologue and environment-lock call, with saved-word readback from a shared native-frame store bank; **`findenv_empty` now composes the complete native empty-environment search and restoring null return**, with `findenv_ready` preserving all platform/allocator facts; getenv/parameter-parser return and subsequent startup calls remain open; allocator inputs and the disabled-pooling flag are supplied through all preceding startup frames; all GPRs are proved initialized at reset, crt0/main retains its full nonwritten-register frame, and concrete domain/pool tests survive stack writes; caml_main-to-domain and fresh-domain-to-stat-allocation prefixes proved with generated calls, store logs and register frames; startup callee bodies remain open; actual reset witness has sbrk-base sentinel -1 and provably fails the library initialized HeapAt predicate, so first malloc bootstrap is a named next obligation; closed `ResetMallocWitness.initial_arena` supplies the zero break, dummy top, sentinel, zero statistics and all 127 empty bins; `sbrk_r_boot` proves the first successful zero-break morecore call via the allocator step table; `malloc_boot_prefix` proves request rounding, empty-bin search and the first 976-byte morecore call boundary with exact stack log and saved-register frame; `malloc_boot_morecore` composes the first successful call without a heap premise, and `malloc_boot_alignment` proves the sentinel initialization and second 2800-byte call boundary; `malloc_boot_initialize` now composes both morecore calls and top initialization to establish ordinary `PHeapAt` from initial metadata (3776-byte arena, empty bins), retaining register/memory frames; `malloc_bootstrap_entry` now completes first malloc through the landed `ext_stats` and `ext_top`/`top_split` proofs, with `MRet.first_pointer` identifying `heapStart + 16`; closed `ResetMallocWitness.vsaOk` now supplies the full library platform invariant (all GPRs present and idle HTIF); `ResetMallocWitness.allocator_loaded` supplies all allocator read-only bytes from executable image and the loader reentrancy word, with bounded balanced certificates; ownership instantiation and machine-summary composition remain; nonpooling `caml_stat_alloc_noexc` dispatch to malloc and initial pool/domain zero reads proved from the abstract BSS-clear effect; complete inner builtin lookup `lookup_run` proved using `loopFromBody` and full strcmp; image/table facts and outer primitive-table construction still open; captured-state theorem is not a reachability proof |
| `WhileMinObservation.bounds`, `noPending`, `nursery_not_empty` | `OCaml/Vm/Boot/WhileMinObservation.lean` | A0 | **proved for the observed projection**; complete native capture validates it; kernel startup execution remains open |
| `WhileMinLog.logOk`, `memory_view` | `OCaml/Vm/Boot/WhileMinLogChecks.lean` | A0 | **proved**: exact memory effect of 35,304 observed stores, checked in small chunks; kernel Sail execution remains open; closed `Loaded` now proved separately |
| `WhileMinRuntime.runtimeOk`, `runtimeOk_fillZero` | `OCaml/Vm/Boot/WhileMinRuntime.lean` | A0 | **proved for the certified memory candidate**: nursery bounds, no pending work and singleton best-fit free-list shape; actual startup execution remains open |
| `WhileMinHeap.repr`, `WhileMinEntry.code`, `loaded_fillZero` | `OCaml/Vm/Boot/WhileMin{Heap,Entry}.lean` | A0 | **proved**: all 29 objects, non-overlap, closure, 191 code words and runtime assembled; `WhileMin.loaded_fillZero` discharges memory, control/image and all 403 primitive bindings for the complete capture |
| `tr_appterm1`, `tr_appterm2`, `tr_appterm3`, `payload_copy_prefix`, `tailcall_restore` | `OCaml/Vm/Sim/{Appterm*,ValueLog,TailcallRestore}.lean` | A1 | **proved conditionally**; generated no-growth/no-pending bodies and shared argument-copy/platform restoration; consumed by represented fixed-arity adapters |
| `appterm1_arm`, `appterm2_arm`, `appterm3_arm`, corresponding `*_step_arm` | `OCaml/Vm/Sim/Appterm{1,2,3}.lean` | A1 | **proved conditionally**; generated represented argument moves and closure entry; bounds, capacity, memory separation and runtime framing remain explicit |
| `grab_fast_arm`, `grab_fast_step_arm` | `OCaml/Vm/Sim/GrabFast.lean` | A1 | **proved conditionally**; generated six-instruction satisfied-arity path with signed-count bound and nonnegative operand; partial-application allocation path remains open |
| `tr_appterm_prefix`, `tr_appterm_copy_more/last`, `tr_appterm_suffix`, `reverse_copy_log_words`, `reverse_copy_source_outside` | `OCaml/Vm/Sim/{Appterm*,ReverseCopyLog}.lean` | A1 | **proved**; generic-tail-call native loop cuts and backward-copy readback/overlap certificates; consumed by the counted machine loop |
| `backward_copy_run` | `OCaml/Vm/Sim/BackwardCopy.lean` | A1 | **proved conditionally on concrete geometry/snapshot**; actual APPTERM backward-copy loop for every bounded word count, overlapping ranges allowed; `loopFromBody` with proved generated iterations; consumed by the complete APPTERM composition |
| `appterm_arm`, `appterm_step_arm` | `OCaml/Vm/Sim/{Appterm,ApptermSetup,ApptermFinish}.lean` | A1 | **proved conditionally**; complete generic tail-call prefix, arbitrary-length backward-copy loop and closure-entry suffix; concrete access/separation/capacity and runtime framing remain explicit |
| `tr_restart_prefix_more/empty`, `tr_restart_copy_more/last`, `tr_restart_suffix`, `restart_restore` | `OCaml/Vm/Sim/{Restart*,BlockRead}.lean` | A1 | **proved conditionally**; generated RESTART cuts and block-field/stack/platform restoration; counted copy loop and full represented composition open |
| `closure_arm`, `closure_step_arm`, `closure_finish` | `OCaml/Vm/Sim/{Closure,ClosureFinish}.lean` | A1 | **proved conditionally**; complete zero/nonempty-capture nursery path with generated copy loop and metadata restoration; count ≤254, capacity, access/separation and runtime preservation explicit; major path open |
| `closurerec_arm`, `closurerec_step_arm`, `closurerec_restore` | `OCaml/Vm/Sim/{Closurerec,ClosurerecRestore}.lean` | A1 | **proved conditionally**; complete native nursery constructor, arbitrary captures/infix functions, object and reversed-stack restoration; nursery capacity, access/separation and runtime preservation remain explicit; major path open |
| `ArmSim` entry + F1 arms (134 opcodes) + halt | `OCaml/Vm/Sim/` | A1 | open; strengthened `Running` contract excludes the HTIF obstruction |
| **`ocamlrun_refinement_Statement L B`** (Layer A, F1) | `OCaml/Theorems.lean` | A1 (by `ocamlrun_refinement_of_arms`) | open; derives unchanged from the repaired arm contract |
| `PlatformOk`, `Running`, `forceExit_not_running`, `platformOk_reloc`, `loopRegisters_reloc` | `OCaml/Vm/Platform*.lean`, `OCaml/Refinement.lean` | A1 | **contract repaired**; composition and regression/transport theorems proved |
| `repr_forceExit`, `armSim_not_repr`, `loaded_not_armSim` | `OCaml/Vm/Sim/Obstruction.lean` | A1 | **proved** against legacy `DataOnlyArmSim`; retained as a regression witness |
| `PrimitiveBindings`, `loaded_probes_disjoint`, `primitiveBindingsEqv` | `OCaml/Vm/Repr.lean`, `Reloc.lean`, `Sim/PrimitiveBinding.lean` | A1 | **contract repaired**: 403 ELF primitive entries bind loaded/loop data; legacy ambiguity obstruction retained; headline unchanged |
| `tr_const0`, `const0_loaded` (first generated machine arm body and full-image pin projection) | `OCaml/Vm/Sim/Const0*.lean` | A1 | **proved**; represented composition below |
| `const0_arm`, `ArmInput.of_repr` (represented dispatch/body composition) | `OCaml/Vm/Sim/Const0.lean`, `ArmInput.lean` | A1 | **proved conditionally** on code geometry, tick, non-cache opcode position and runtime memory frame; full `ArmSim.next` open |
| `const1_arm`, `const2_arm`, `const3_arm`, `immediate_arm` | `OCaml/Vm/Sim/Const*.lean`, `Immediate.lean` | A1 | **proved conditionally**; generated constant family restores data/platform through one shared dispatch/body composition |
| `constint_arm`, `tag_word32`, `OperandAt.read` | `OCaml/Vm/Sim/Constint*.lean`, `ArmInput.lean` | A1 | **proved conditionally**; signed operand load/tagging, PC +2 and represented restoration; ordinary-word/code-geometry premises explicit |
| `branch_arm`, `relative_code_word`, `OperandAt.read32` | `OCaml/Vm/Sim/Branch*.lean`, `ArmInput.lean` | A1 | **proved conditionally**; signed forward/backward targets and full represented restoration, with operand/dispatch/runtime-frame premises |
| `branchif_arm`, `branchifnot_arm`, `control_arm`, `false_word_iff` | `OCaml/Vm/Sim/Branchif*.lean`, `Immediate.lean`, `IsintArithmetic.lean` | A1 | **proved conditionally**; both guarded paths from successful `stepI`, with alignment/non-raw, operand/dispatch/runtime-frame premises explicit |
| Atom-table base binding, relocation and captured mismatch | `OCaml/Vm/Repr.lean`, `Reloc.lean`, `Sim/Atom*.lean`, `Boot/WhileMinEntry.lean` | A1/A0 interface | **proved**; placement stores the allocated atom-table base, Loaded/VM payload bind its global pointer, boot supplies it and frames preserve it; unchanged headline |
| `atom0_arm`, `atom_arm`, `index_word`; upper-immediate generator classes | `OCaml/Vm/Sim/Atom*.lean`, `IndexWord.lean`, `scripts/syi/alu_classes.py` | A1 | **proved conditionally**; Layout-derived runtime table load and shared restoration, explicit nonnegative ATOM index; retained negative-index mismatch witness |
| `addint_step_arm`, `subint_step_arm`, `andint_step_arm`, `orint_step_arm`, `xorint_step_arm` | `OCaml/Vm/Sim/*int.lean`, `StackConsume.lean`, `ReadOnly.lean` | A1 | **proved conditionally**; one generated integer-binary family, shared stack/root restoration and semantic input extraction; dispatch/runtime frame/read geometry remain explicit |
| `lslint_step_arm`, `lsrint_step_arm`, `asrint_step_arm`, `shift_count` | `OCaml/Vm/Sim/*int.lean`, `ShiftArithmetic.lean` | A1 | **proved conditionally**; shared six-bit native count, full-domain tagged results and successful-step wrappers, reusing binary restoration |
| `ltint_step_arm`, `leint_step_arm`, `gtint_step_arm`, `geint_step_arm`, `ultint_step_arm`, `ugeint_step_arm` | `OCaml/Vm/Sim/*int.lean`, `ComparisonArithmetic.lean` | A1 | **proved conditionally**; both native branch paths of all six signed/unsigned integer comparisons, sharing the binary generator and stack restoration |
| `bltint_step_arm`, `bleint_step_arm`, `bgtint_step_arm`, `bgeint_step_arm`, `bultint_step_arm`, `bugeint_step_arm` | `OCaml/Vm/Sim/B*int.lean`, `BranchCompare.lean` | A1 | **proved conditionally**; both immediate-comparison branch outcomes, exact Long_val and operand-2 target identity, with dispatch/runtime/read premises explicit |
| `tr_isint`, `isint_loaded` (generated five-instruction machine body with SLLI/ANDI) | `OCaml/Vm/Sim/Isint*.lean` | A1 | **proved**; full representation/frame bridge open |
| `isint_arm`, `isintWord_repr`, `isint_not_valWord` | `OCaml/Vm/Sim/Isint*.lean` | A1 | **proved conditionally** on dispatch readiness, runtime frame, even placement and non-raw accumulator; checked value-level alignment obstruction retained |
| `tr_negint`, `negint_loaded` (generated four-instruction tagged-negation body) | `OCaml/Vm/Sim/Negint*.lean` | A1 | **proved**; represented composition below |
| `negint_arm`, `immediate_restore`, `tag_neg`, `untag_neg` | `OCaml/Vm/Sim/Negint.lean`, `Immediate*.lean` | A1 | **proved conditionally** on `ArmInput` / runtime memory frame, with exact modular `stepI` result |
| `indexed_log_read`, `apply_frame_payload` | `OCaml/Vm/Sim/{IndexedStores,ValueWords,ApplyFrameLog,ApplyFramePayload}.lean` | A1 | **proved**; unique-index write readbacks and all three fixed-arity frame permutations share represented prefix/root restoration; used by generated arm compositions |
| `apply_frame_restore` | `OCaml/Vm/Sim/ApplyRestore.lean` | A1 | **proved conditionally**; fixed-arity applications share data/platform restoration from concrete frame writes and final register observations; consumed by generated body compositions |
| `apply1_arm`, `apply2_arm`, `apply3_arm`, corresponding `*_step_arm` | `OCaml/Vm/Sim/Apply{1,2,3}.lean` | A1 | **proved conditionally**; generated adapters compose native frame insertion and closure entry, including no-growth/no-pending tails; geometry, capacity and runtime-window preservation remain explicit |
| `tr_apply1`, `tr_apply2`, `tr_apply3`, `payload_replace_prefix` | `OCaml/Vm/Sim/{Apply1,Apply2,Apply3,FrameInsert,LogWindow}*.lean` | A1 | **machine paths/shared stack-prefix replacement proved**; exact 17/18/21-instruction no-growth/no-pending paths, code pins and write frames; represented fixed-arity composition open |
| `return_more_arm`, `return_frame_arm`, corresponding `*_step_arm` | `OCaml/Vm/Sim/Return*.lean` | A1 | **both paths proved conditionally**; generated eight/ten-instruction paths, closure entry or saved caller restoration, root preservation before stack drop; nonnegative operand/saved count, bounded extra, read geometry and runtime frame explicit |
| `apply_arm`, `apply_step_arm`, `heap_of_live`, `payload_env_of_root` | `OCaml/Vm/Sim/{Apply,ApplyArithmetic,RootFrame,EnterReady}.lean` | A1 | **proved conditionally**; generated ten-instruction no-growth/no-pending path, closure code/environment selection and positive-arity decrement; shared capacity, pending, geometry and runtime-frame premises explicit |
| `pushtrap_arm`, `pushtrap_step_arm` | `OCaml/Vm/Sim/Pushtrap.lean` | A1 | **proved conditionally**; generated five-store body, intervening domain/trap read frames and exact semantic result; bounded depths, geometry, separation and runtime windows explicit |
| `pushtrap_payload`, `pushtrap_restore`, `pushtrap_link` | `OCaml/Vm/Sim/Pushtrap{Arithmetic,Store,Restore}.lean` | A1 | **proved**; exact five-write frame readbacks, relative link arithmetic and represented trap/frame restoration; generated-body composition proved conditionally |
| `poptrap_arm`, `poptrap_step_arm`, `trap_restore` | `OCaml/Vm/Sim/{Poptrap,TrapPayload,TrapArithmetic}.lean` | A1 | **proved conditionally**; no-pending native trap-link reconstruction, exact trap-pointer store, stack drop and full represented restoration; runtime/geometry/separation premises explicit |
| `tr_poptrap`, `tr_pushtrap`, full-image pins | `OCaml/Vm/Sim/{Poptrap,Pushtrap}*.lean` | A1 | **machine bodies proved**; 13-instruction no-pending pop and 23-instruction push, exact writes/register frame; represented POPTRAP adapter proved; PUSHTRAP adapter proved conditionally |
| `offsetref_arm`, `offsetref_step_arm`, `field_restore`, `payload_heap_frame` | `OCaml/Vm/Sim/{Offsetref,FieldRestore,HeapPayload}.lean` | A1 | **proved conditionally**; exact integer heap-field update and full represented restoration; geometry, non-heap separation and runtime-window preservation remain explicit |
| `live_field_edit`, `heap_field_written` | `OCaml/Vm/Sim/{HeapEdit,FieldStore}.lean` | A1 | **proved**; exact field-store object readbacks, root closure and preserved heap separation; consumed by OFFSETREF |
| `push_retaddr_arm`, `push_retaddr_step_arm`, `retaddr_payload` | `OCaml/Vm/Sim/{PushRetaddr,RetaddrStore}.lean` | A1 | **proved conditionally**; exact three-store return frame, represented roots/registers and full platform restoration; stack/dispatch geometry, separation and runtime window explicit |
| `tr_offsetref`, `tr_push_retaddr`, `stack_prepend` | `OCaml/Vm/Sim/{Offsetref,PushRetaddr,StackPrefix}*.lean` | A1 | **machine bodies and shared frame-prefix facts proved**; represented return-frame adapter proved; heap-update adapter proved conditionally |
| `switch_block_arm`, `switch_block_step_arm`, `SwitchTag.of_object` | `OCaml/Vm/Sim/{SwitchBlock,SwitchRead,SwitchSemantics}.lean` | A1 | **block path proved conditionally**; ordinary object/header and code-halfword adapters; atom/infix headers, geometry and invariant adapters explicit |
| `switch_int_arm`, `switch_int_step_arm` | `OCaml/Vm/Sim/{SwitchInt,SwitchArithmetic}.lean` | A1 | **integer path proved conditionally**; represented table lookup and exact relative target; block-tag path proved below; invariant adapters open |
| `tr_switch_int`, `tr_switch_block`; total LHU sites | `OCaml/Vm/Sim/Switch*.lean`, `scripts/syi/` | A1 | **machine paths proved**; both native paths and full-image pins; conditional represented selection/target adapters proved |
| `check_signals_arm`, `signalCheckReady_of_runtime` | `OCaml/Vm/Sim/CheckSignals*.lean` | A1 | **proved conditionally**; generated shared-block no-pending path, fixed Layout-derived read geometry and concrete runtime readiness adapter; dispatch/runtime-frame obligations explicit |
| `mulint_arm`, `mulint_step_arm` | `OCaml/Vm/Sim/Mulint*.lean` | A1 | **proved conditionally**; generated call boundaries composed with the proved libgcc summary; scratch-register, read/dispatch geometry and runtime-frame obligations explicit |
| `muldi3_summary`, `tag_mul_native` | `OCaml/Vm/Sim/{Muldi3,MulArithmetic}.lean` | A1 | **proved**; named libgcc machine summary, full-image code projection and modular retagging; consumed by represented MULINT |
| `tr_mulint_prefix`, `tr_mulint_suffix` | `OCaml/Vm/Sim/Mulint*.lean` | A1 | **machine boundaries proved**; five-step direct-call prefix and four-step return, with full-image pins and frame; represented libgcc composition proved |
| `tr_offsetint`, `offsetint_width_obstruction` | `OCaml/Vm/Sim/Offsetint*.lean`, `OffsetWidth.lean` | A1 / A2 semantics | **body and historical obstruction proved**; BcSem now shifts OFFSETINT/OFFSETREF operands in 32 bits before sign extension, matching SLLIW; 16 host/runbc signed-boundary differentials pass (`results/bc-offsets.json`) |
| `boolnot_arm`, `tag_sub`, `tag_not` | `OCaml/Vm/Sim/Boolnot*.lean`, `ImmediateArithmetic.lean` | A1 | **proved conditionally**; NEGINT/BOOLNOT generated from one shared tagged-subtraction bridge, for all 63-bit integer inputs |
| `tr_acc0`, `tr_acc`, `acc0_loaded`, `acc_loaded` (generated stack loads through total RAM reads) | `OCaml/Vm/Sim/Acc*.lean` | A1 | **proved**; address geometry and representation/frame bridge open |
| `acc0_arm`–`acc7_arm`, `accu_restore`, `accu_arm`, `stack_slot_nat` | `OCaml/Vm/Sim/Acc*.lean`, `StackAcc.lean`, `Immediate.lean` | A1 | **proved conditionally**; one generated stack-load family, shared live-root restoration, non-wrapping addresses derived from representation; RAM/HTIF windows explicit |
| `envacc1_arm`–`envacc4_arm`, `getfield0_arm`–`getfield3_arm`, `FieldSelection.read`, `RamReadAt.window` | `OCaml/Vm/Sim/Envacc*.lean`, `Getfield*.lean`, `FieldRead.lean`, `ReadGeometry.lean` | A1 | **proved conditionally**; one generated field-load family, represented lookup/root witnesses derived; RAM/HTIF geometry explicit |
| `acc_arm`, `envacc_arm`, `getfield_arm` | `OCaml/Vm/Sim/{Acc,Envacc,Getfield}.lean` | A1 | **proved conditionally** through one indexed-read generator; successful selection, nonnegative operand and total-read geometry remain explicit |
| `pop_arm`, `pop_step_arm`, `consume_value_arm` | `OCaml/Vm/Sim/{Pop,StackConsume}.lean` | A1 | **proved conditionally**; bounded prefix removal, arbitrary live result, with shared dispatch and payload restoration |
| `getvectitem_arm`, `getbyteschar_arm`, `getstringchar_arm` | `OCaml/Vm/Sim/{Getvectitem,Getbyteschar,Getstringchar}.lean` | A1 | **proved conditionally**; represented selection and stack consumption; full-width scaled vector index, RAM-bounded byte index and byte retagging checked |
| `offsetclosure*_arm`, `ClosureOffset` | `OCaml/Vm/Sim/Offsetclosure*.lean`, `ClosureOffset.lean` | A1 | **proved conditionally** for all four read-only offsets, including signed operands with nonnegative resulting field index |
| `push_arm`, `pushacc0_arm`–`pushacc7_arm`, `pushconst0_arm`–`pushconst3_arm`, `pushenvacc1_arm`–`pushenvacc4_arm`, `push_value_arm`, `PushWriteOk` | `OCaml/Vm/Sim/Push*.lean`, `StackStore.lean` | A1 | **proved conditionally**; exact write-log payload/image/binding frames, stack root/shape restoration; static separation and `WindowStable` are named invariant-adapter obligations; fixed stack/environment selections and constants share the generated bridge |
| `pushoffsetclosurem3_arm`, `pushoffsetclosure0_arm`, `pushoffsetclosure3_arm` | `OCaml/Vm/Sim/Pushoffsetclosure*.lean` | A1 | **proved conditionally**; shared push restoration and signed closure-offset arithmetic, with static write/runtime separation explicit |
| `pushconstint_arm`, `pushoffsetclosure_arm`, `PushWriteOk.operand_read32` | `OCaml/Vm/Sim/Pushconstint.lean`, `Pushoffsetclosure.lean`, `StackStore.lean` | A1 | **proved conditionally**; operand survives the stack write via payload separation; signed immediate and closure results reuse existing arithmetic |
| `pushacc_arm`, `pushenvacc_arm`, `pushatom0_arm`, `pushatom_arm` | `OCaml/Vm/Sim/Pushacc.lean`, `Pushenvacc.lean`, `Pushatom*.lean` | A1 | **proved conditionally**; shared write restoration, pushed-stack selection (including zero), field and atom-binding frames; sign/geometry/runtime obligations explicit |
| `getglobal_arm`, `pushgetglobal_arm` | `OCaml/Vm/Sim/Getglobal.lean`, `Pushgetglobal.lean` | A1 | **proved conditionally**; global-root selection and runtime pointer binding, with stack-write framing for the PUSH form; index sign/access/runtime premises explicit |
| `getglobalfield_arm`, `pushgetglobalfield_arm`, `FieldSelection.read_reachable`, `FieldSelection.load_frame` | `OCaml/Vm/Sim/Getglobalfield.lean`, `Pushgetglobalfield.lean`, `FieldRead.lean` | A1 | **proved conditionally**; composed reachable-field selection and write-log preservation of the intermediate pointer; sign/access/runtime premises explicit |
| `beq_step_arm`, `bneq_step_arm`, `beq_pointer_guard_obstruction` | `OCaml/Vm/Sim/Beq.lean`, `Bneq.lean`, `BranchCompare.lean` | A1 | **proved conditionally for integers**; both generated paths and successful stepI adapters; non-integer native/semantic guard discrepancy retained as a checked word witness |
| `eq_step_arm`, `neq_step_arm`, `WordEquality.ints` | `OCaml/Vm/Sim/Eq.lean`, `Neq.lean`, `WordEquality.lean` | A1 | **proved conditionally**; both physical-equality paths and actual stepI adapters; named word-reflection premise, discharged for tagged integers |
| `vectlength_step_arm`, `SizeSelection.of_object`, `header_size_tag` | `OCaml/Vm/Sim/Vectlength.lean`, `SizeRead.lean` | A1 | **proved conditionally**; header decoding/tagging and actual stepI adapter, size observation derived for ordinary allocation bases; atom/infix header agreement remains explicit |
| `assign_step_arm`, `payload_frame_stack`, `stack_assign`, `StackPost.registers`, `StackPost.after_dispatch` | `OCaml/Vm/Sim/Assign.lean`, `AssignStore.lean`, `StackEdit.lean`, `StackConsume.lean` | A1 | **proved conditionally**; exact stack-slot write and unit result, shared payload/root restoration and dispatch/register reconstruction; static write separation and index sign remain explicit |
| `tr_c_call1_prefix`, `tr_c_call1_suffix`, `StepFrameOut.of_jalr` | `OCaml/Vm/Sim/Ccall1*`, `Vsa/Sim/JalrFrame.lean` | A1 | **machine segments proved**; generated indirect call setup and return restoration, exact stores and full-image pins; represented primitive-summary splice remains open |
| `c_call1_return`, `c_call1_primitive_return`, `c_call1_sys_argv` | `OCaml/Vm/Sim/Ccall1{Return,Primitives}.lean` | A1 | **return bridge proved conditionally**; restores Running from represented primitive post and saved caller frame, consumes landed Sys.argv summary; prefix and returning arm proved below |
| `c_call1_setup`, `Ccall1WriteOk.savedEnv`, `ccall1_savedStack`, `StepFrameOut.widenChecked` | `OCaml/Vm/Sim/Ccall1{Setup,Store}.lean`, `Vsa/Sim/FrameWriteSet.lean` | A1 | **setup bridge proved conditionally**; exact three-store effects establish represented primitive input, saved frame and ELF-bound target; compact generator frames keep default limits |
| `c_call1_arm`, `c_call1_step_arm`, `c_call1_callee_of_readOnly`, `c_call1_sys_argv_callee` | `OCaml/Vm/Sim/Ccall1.lean` | A1 | **proved conditionally for returning F1 primitives**; callSeg composes dispatch/setup, named represented callee summary and restoration; Sys.argv instance consumes a1-prims, exceptions/exits remain open |
| `Ccall1Callee`, `Ccall1Ready` | `OCaml/Vm/Sim/Ccall1.lean` | A1 / a1-prims | **named obligations**: returning represented primitive summary with saved caller frame, plus invariant-to-call geometry/separation; read-only constructor and conditional Sys.argv instance proved |
| `c_call2_arm`–`c_call5_arm`, matching step adapters, `c_call2_int_compare_callee` | generated `OCaml/Vm/Sim/Ccall{2,3,4,5}.lean`, `Ccall2Primitives.lean` | A1 | **proved conditionally for returning F1 primitives**; shared `CcallReady`/`CcallCallee`, generated setup and bounded stack restoration composed by callSeg; integer-compare instance consumes a1-prims summary; exception/exit paths and invariant adapters remain open |
| `tr_c_call2_prefix`–`tr_c_call5_prefix`, corresponding suffixes/pins | `OCaml/Vm/Sim/Ccall{2,3,4,5}*` | A1 | **machine segments proved**; one arity-driven generator, exact stores and indirect calls, six-instruction returns; represented bridges proved in adjacent rows |
| `tr_c_calln_prefix`, `tr_c_calln_suffix`, image pins | `OCaml/Vm/Sim/Ccalln{Prefix,Suffix}*` | A1 | **machine segments proved**; stack-array ABI, five stores including native saved PC, indirect call and eight-instruction return; represented returning bridge proved in adjacent rows |
| `c_calln_return`, `c_calln_primitive_return`, `ccall_result_restore` | `OCaml/Vm/Sim/CcallnReturn.lean`, `CcallReturn.lean` | A1 | **proved conditionally**; shared primitive-result payload/platform restoration, saved native bytecode PC/count and VM frame, positive-arity bounded stack consumption; setup and returning composition proved below |
| `c_calln_setup`, `c_calln_arm`, `c_calln_step_arm`, `c_calln_callee_of_readOnly` | `OCaml/Vm/Sim/Ccalln{Store,Input,Setup}.lean`, `Ccalln.lean` | A1 | **proved conditionally for returning F1 primitives**; exact five-store readbacks, represented stack-array ABI, native saved frame, dispatch/setup/callee/return callSeg; actual stack-array callee summaries and invariant adapters remain explicit |
| `offsetintOperand_eq`, `tag_offsetint`, `offsetint_arm`, `offsetint_step_arm` | `OCaml/Vm/Sim/OffsetArithmetic.lean`, `Offsetint.lean` | A1 | **proved conditionally**; generated LW/SLLIW/add matches the corrected 32-bit-shift semantics, including overflow operands; shared odd-word retagging, memory/platform restoration; operand/dispatch geometry explicit |
| `ccall_return_restore`, `c_call1_return`–`c_call5_return` | `OCaml/Vm/Sim/CcallReturn.lean`, generated `Ccall{1,2,3,4,5}Return.lean` | A1 | **proved conditionally**; shared represented primitive contract, generated six-instruction restoration and bounded stack consumption; setup and returning composition proved in adjacent rows |
| `ccall_argument_load`, `ccall_arguments_repr`, `c_call2_setup`–`c_call5_setup` | `OCaml/Vm/Sim/CcallSetup.lean`, generated `Ccall{2,3,4,5}Setup.lean` | A1 | **proved conditionally**; three saved-frame stores, represented accumulator/stack arguments, ELF-bound indirect target; setup geometry and callee-summary composition explicit |
| Nonzero DIVINT/MODINT represented arms | `OCaml/Vm/Sim/Division.lean:division_arm`, `division_step_arm` | A1 | **proved conditionally**: generated caller setup/return composed with complete signed libgcc summaries, 63-bit unboxing/retagging agreement including minimum overflow, stack consumption and Running restoration; zero-divisor exception paths and uniform invariant premises remain open |
| F1 primitive summaries (`primsF1`, 30 entries) | `OCaml/Vm/Primitives/` | A1 | **18/30 proved (G1)**: system constants, signed integer comparison, argv, string/bytes lengths, fresh object IDs, canonical string equality/inequality, int64-to-double bits and executable-name allocation, generated ELF `FnSummary` plus represented VM payload/result and platform/ABI frame; read-only runtime preservation uses `MemoryStable` (proved for `RuntimeOk` from its free-list frame law); counter/native-stack writes use `WindowStable` plus separation. Allocating calls expose nursery-room, placement/separation and runtime-effect premises. Other 12 primitives open |
| Named-value model replacement and C-string keys | `OCaml/Bytecode/NamedValues.lean` | A1 semantics | **corrected and checked** against callback.c; host table probe and all ten host/runbc difftests pass; lookup/frame/root-membership laws proved |
| Library call bridge | `OCaml/Vm/Primitives/LocalRunBridge.lean`, `LibraryStrlen.lean` | A1 | `LocalRun`/`SWP` to machine `FnSummary` proved through `loopFromBody`; strlen return, register and total-byte memory facts instantiated from the landed library spec. No additional primitive counted |
| Full memcpy local-run port | `VsaIris/Vsa/Memcpy{Run,Steps,Loops}.lean`, `OCaml/Vm/Primitives/LibraryMemcpy.lean` | A1 support | Complete alignment/bulk/word/byte paths retargeted through allocator templates; `memcpy_summary` supplies copied bytes, return ABI and confined memory/output frame. No additional OCaml primitive counted |
| String constructor representation support | `Primitives/LibraryEffects.lean`, `StringAllocationArithmetic.lean`, `StringAllocationLayout.lean` | A1 support | Generated writes preserve library well-formedness; canonical initializer log establishes header, padding and zero padding. Actual caller composition remains open; primitive count unchanged |
| Nursery allocation support | `OCaml/Vm/Primitives/Allocation.lean`, `DoubleFast.lean`, `DoubleLayout.lean` | A1 | Heap extension and `caml_copy_double` successful nursery path proved from generated block certificates; int64 primitive tail/representation bridge proved under G1 room; collector-enabled path remains A6 |
| Nursery block families | `OCaml/Vm/Primitives/SmallAllocation.lean`, `StringAllocation.lean`, `StringFast.lean` | A1 | Common generated access-plan adapter and small/string block certificates proved; string prefix, reservation and initialization exact effects proved. Initialization scalar accesses and whole-string composition now proved, with readbacks supplied by metadata/separation; string layout and callers remain open; no additional primitive counted |
| `tr_dispatch`, `dispatch_loaded` (in-range dispatch machine path) | `OCaml/Vm/Sim/Dispatch*.lean` | A1 | **proved**; Running/jump-table-to-arm bridge open |
| `dispatchOffset_loaded`, `dispatchOffset_target`, opcode guard/target geometry | `OCaml/Vm/Sim/DispatchTable*.lean` | A1 | **proved** for all 149 pinned table entries; dispatch composition open |
| `dispatch_run` (named dispatch-to-arm boundary and complete frame) | `OCaml/Vm/Sim/Dispatch.lean` | A1 | **proved**; bytecode RAM/HTIF geometry and tick premises remain explicit |
| F2/F3/F4/F5 arms and primitives | `OCaml/Vm/Sim/` | A2–A5 | open |
| GC: `caml_empty_minor_heap` preserves `VmReprAt` up to a new placement (G2) | `OCaml/Vm/Gc/` | A6 | open: strict Forward bridge obstructed; machine oldify/mopup proof remains open |
| Forward short-circuit obstruction / transparent-value ISINT incompatibility | `OCaml/Vm/Gc/Forward.lean` | A6 | **proved**; pinned host regression confirms `false true`; option (a) chosen: GcSafe is now an explicit precondition; BcSem remains deterministic |
| GC-observation safety / Layer A premise | `OCaml/Bytecode/GcSafe.lean`, `Refinement.lean`, `EndToEnd.lean` | A6 round 2 | `GcSafe` defined on reachable directed shortcuts within forwarding equivalence; threaded through headline statements; existing composition proofs rebuilt; concrete collection-boundary coverage open |
| `GcSafe boot/ocamlc` | `Theorems.boot_ocamlc_gcSafe_Statement`, `scripts/check_gc_safety.py`, `results/gc-safety.json` | A6 / C | **open**: 5741 conservative observation sites need lazy-flow analysis; hello.cmo/output identical at default and 4K/8K/16K heaps (1/61/32/17 minor collections); typing alone insufficient, as checked typed physical-equality regression shows |
| Real Lazy.force forwarding observation | `OCaml/Programs/LazyForce.lean` | A6 round 2 | **proved** under named code/global/tag premises: twelve/fourteen-step confluence for arbitrary continuation; integer case discharges tag premise; generated real stdlib bytecode and host/BcSem regression checked |
| Observational collection boundary composition | `OCaml/Vm/Gc/Observed.lean` | A6 / G2 | **proved conditionally** by `ObservedAt.collect`; concrete `CollectionEffect` from oldify/mopup remains **open** |
| oldify immediate-value machine route | `OCaml/Vm/Gc/Generated/Immediate.lean` | A6 / G2 | **proved** from concrete SegPre: composed entry-to-return FnSummary, final root word and stack arithmetic; LoopHead supplier, heap-pointer cases and mopup composition **open** |
| mopup machine segment coverage | `OCaml/Vm/Gc/Generated/Mopup*.lean`, `results/gc-mopup-regions.json` | A6 / G2 | **proved segments**, all 149 instructions in disjoint regions under unchanged limits; shared signed/unsigned comparison soundness added; loop invariants/call splicing **open** |
| mopup prologue and queue pop | `Generated/MopupControl.lean`, `Generated/MopupPop.lean` | A6 / G2 | **proved from generated posts/SegPre**: runtime register setup and single todo-list update on both first-field branches; queue invariant and load suppliers **open** |
| Intrusive queue pop from concrete memory | `OCaml/Vm/Gc/QueueAccess.lean:pop_machine`, `Queue.lean:pop_loaded` | A6 / G2 | **proved** from platform/code/register pins, RAM windows and separated queue links; all scalar reads, store and branches discharged; copied-field invariant and oldify calls **open** |
| oldify allocation-return queue insertion | `Generated/Enqueue.lean`, `QueueEnqueue.lean:enqueue` | A6 / G2 | **proved machine path**: six stores, all scalar loads and size branch discharged by EnqueueAccess.enqueue_machine; allocation/freshness suppliers **open** |
| Grey copied-object payload layout | `OCaml/Vm/Gc/PendingPayload.lean:pendingPayload_enqueue` | A6 / G2 | **proved** using Eqv: saved first field at copy, remaining fields at source under original placement; source-suffix footprint supplier and blackening loop **open** |
| Immediate-valued mopup field iteration | `OCaml/Vm/Gc/FieldCopyAccess.lean:copy_machine` | A6 / G2 | **proved** from concrete RAM/register/tag facts: destination word, counter/pointer increments, exit PC, code and native frame; immediate suffix loop proved below; pointer-call paths **open** |
| Immediate-valued mopup suffix loop | `OCaml/Vm/Gc/ScanLoop.lean:scan_loop` | A6 / G2 | **proved** with the standard decreasing-count loop rule, concrete header/branch facts, copied prefix and memory/native/code frames; integer grey-payload bridge proved below; pointer calls **open** |
| Typed integer-suffix scan result | `OCaml/Vm/Gc/ScanPayload.lean:scan_grey` | A6 / G2 | **proved**: concrete scan yields ObjAt from grey payload via Eqv, preserving header and saved first field; fixed placement, integer suffix; machine setup composed below; pointer oldification **open** |
| Machine setup through represented suffix | `OCaml/Vm/Gc/ScanSetup.lean:setup_scan` | A6 / G2 | **proved**: actual setup/header branch and complete integer suffix, ObjAt and memory/output/native frames; starts after first-field handling; integer queue-pop seam composed below; pointer paths **open** |
| Pending integer block traversal | `OCaml/Vm/Gc/PopScan.lean:pop_scan` | A6 / G2 | **proved**: concrete queue pop through represented destination, remaining queue and full memory/output/native frame; explicit heap/global/link separation; back-edge entry composed below; outer loop and pointer paths **open** |
| Mopup subsequent queue entry | `OCaml/Vm/Gc/QueueResume.lean:resume_scan` | A6 / G2 | **proved**: actual bottom-test entry and shared integer-block continuation; common post effect certified separately from runs; empty exit proved below; outer invariant/termination and pointer paths **open** |
| Mopup empty queue tests | `OCaml/Vm/Gc/QueueEmpty.lean:empty_machine` | A6 / G2 | **proved** for both entry PCs: concrete zero-head read reaches ephemeron region with unchanged memory/output and native frame; full ephemeron phase and return **open** |
| Concrete mopup young-range classifier | `OCaml/Vm/Gc/YoungAccess.lean:classify` | A6 / G2 | **proved** from Layout-derived domain reads: strict lower/upper bounds, all three paths and nonpointer copy consequence from NoForgery; parity caller composed below; copying/oldify composition **open** |
| Loaded even-field classification | `OCaml/Vm/Gc/FieldClassify.lean:classify_field` | A6 / G2 | **proved**: actual field load/tag branch and young tests, value/destination/scan registers and complete frames; NoForgery copy consequence; non-young store/advance composed below; oldify calls **open** |
| Non-young even-field copy/advance | `OCaml/Vm/Gc/CopyEffect.lean:copy_even` | A6 / G2 | **proved** through actual load/classifier/store/advance, exact word/log/PC and frames; common effect retains route-specific write sets; mixed non-young loop proved below; young oldify calls **open** |
| Mixed non-young suffix and typed payload | `MixedScan.lean:mixed_scan`, `MixedPayload.lean:scan_mixed_grey` | A6 / G2 | **proved** with actual per-field branch choices, preserved runtime bounds, NoForgery plus stable genuine pointers, Eqv/ObjAt result; original integer frame retained; young relocation, mixed queue seams and outer termination **open** |
| Already-forwarded young-object root update | `ForwardedAccess.lean:forwarded_machine` | A6 / G2 | **proved**: actual zero-header branch, forwarding load and root store, Eqv slot relocation from typed target evidence and separated queue frame; prologue/return, partial-placement supplier and pointer-call composition **open** |
| Oldify native epilogue and forwarded return | `OldifyReturn.lean:return_machine`, `ForwardedReturn.lean:forwarded_return` | A6 / G2 | **proved**: actual eleven saved-word loads, stack adjustment, aligned return, and composition with forwarded root update under native-frame separation; prologue/range entry and pointer caller **open** |
| oldify queue insertion through native return | `EnqueueReturn.lean:enqueue_return` | A6 / G2 | **proved**: six-store enqueue plus common epilogue, concrete queue/root/first-field result and complete frames; native-frame separation explicit; allocating call/prologue suppliers **open** |
| oldify pointer prologue and saved caller frame | `OldifyEntry.lean:entry_machine`, `OldifySaved.lean:Post.saved` | A6 / G2 | **proved**: concrete parity branch, eleven saves and runtime setup, original caller/return-word readback, generated save/restore agreement and RAM-derived no-wrap; nursery tests and whole forwarded call **open** |
| Whole already-forwarded oldify call | `ForwardedCall.lean:forwarded_call` | A6 / G2 | **proved**: real prologue, Layout-based strict-young tests, zero-header root update and native return with original caller registers/PC and exact stores; explicit separation, header and range premises; mopup caller splice and fresh-copy routes **open** |
| Mopup forwarded-field call and resume jump | `MopupResume.lean:forwarded_resume` | A6 / G2 | **proved**: ELF-certified JAL via shared bridge, actual oldify callee, link return and jump to counter advance, relocated root/exact log/restored registers and mopup-code frame; header advance and loaded-field seam **open** |
| Forwarded-field call through scan advance | `ForwardedAdvance.lean:forwarded_advance` | A6 / G2 | **proved**: concrete post-call header branch/source-index advance, exact native-save/root log and relocated word; shared restored-register ABI frame retains scan/domain registers; classifier seam and size footprint proved by `ForwardedField.forwarded_field` and `ForwardedEffect.lean:againAfterCall_count`; forwarded suffix loop proved below; fresh-copy relocation **open** |
| Already-forwarded young-field suffix loop | `ForwardedLoop.lean:forwarded_scan` | A6 / G2 | **proved**: each real loaded-field/classifier/callee/advance iteration derives its input from framed initial observations and geometric separation; exact relocated field words, native/code/runtime context and observed-counter termination; typed payload proved below; fresh copying, mixed young/non-young scan and outer collector **open** |
| Typed relocated forwarded suffix result | `RelocatedPayload.lean:scan_relocated`, `ForwardedInitial.lean:LoopAt.initial` | A6 / G2 | **proved**: concrete already-forwarded scan yields ObjAt at the new placement via Eqv, with a framed target header and previously handled first field; initialization derives the loop invariant from platform/code/register pins; first-field route and partial-placement suppliers **open** |
| Already-forwarded first-field route and typed boundary | `FirstField.lean:forwarded`, `FirstPayload.lean:Post.relocating_grey` | A6 / G2 | **proved**: actual nursery classifier, destination setup, JAL, full oldify callee and return jump to suffix setup; exact native/first-slot log and ABI frame; Eqv supplies relocated first field with separated source suffix; queue-pop seam, fresh-child route and whole collector **open** |
| Queue pop through forwarded first-field update | `PopFirst.lean:pop_first`, `PopFirstPayload.lean:PopFirstPost.relocating_grey` | A6 / G2 | **proved**: actual queue/child loads and parity branch supply the classifier/callee input; composed exact queue-head/native/first-slot log, remaining queue preserved through Eqv, typed relocated grey boundary; suffix-setup composition and fresh-child cases **open** |
| Suffix setup through typed forwarded scan | `ForwardedSetup.lean:setup_relocated` | A6 / G2 | **proved**: actual setup supplies the complete loop context; fixed observations transported across read-only setup; terminating forwarded scan yields ObjAt with memory/native/code/output frames relative to the original boundary; full pending-object seam and fresh-copy cases **open** |
| Complete forwarded pending-object traversal | `PopForwarded.lean:pop_forwarded`, `QueueForwarded.lean:resume_forwarded` | A6 / G2 | **proved**: actual initial/backedge queue pop, forwarded first child, native return, setup and terminating forwarded suffix yield relocated ObjAt and remaining queue with memory/native/code/output frames; all children already-forwarded young and size > 1; mixed/fresh-copy cases and outer queue loop **open** |
| Mixed copied/forwarded suffix | `MixedLoop.lean:mixed_scan`, `MixedRelocated.lean:scan_relocated`, `MixedSchedule.lean:schedule_advance` | A6 / G2 | **proved**: actual immediate/non-young copy and already-forwarded young oldify routes share one terminating loop; framed initial observations derive inputs and route decisions, canonical register maps derive transitions, Eqv supplies relocated ObjAt; fresh-copy allocation **open**; mixed queue composition proved below |
| Pending-object traversal with mixed suffix | `PopMixed.lean:pop_mixed`, `PopMixed.lean:resume_mixed` | A6 / G2 | **proved**: real initial/backedge queue visit, forwarded first child, setup and mixed copied/forwarded suffix yield relocated ObjAt and preserved queue/frames; fixed observations transported across prefix writes; other first-child cases, fresh allocation and full queue closure **open** |
| Fresh scanned-object entry through allocation JAL | `FreshCall.lean:prepare_allocation`, `FreshEntry.lean:prepare_entry` | A6 / G2 | **proved**: actual prologue, strict nursery tests, nonzero header/scanned-tag arm, typed size/tag/header arguments and decoded JAL reach caml_alloc_shr_for_minor_gc with saved caller state and return link; allocation body and fresh-copy composition **open** |
| Fresh entry through free-list call boundary | `FreshAllocator.lean:prepare_free_list`, `AllocEntryAccess.lean:prepare` | A6 / G2 | **proved**: actual oldify/allocator prologues and JAL establish the combined native-save/tag log, loaded free-list function pointer and outgoing registers; source-header size implies the real maximum-size check; allocation body and return **open**; indirect call discharged below |
| Fresh entry executes the free-list indirect call | `FreshIndirect.lean:enter_free_list`, `AllocIndirect.lean:call_free_list` | A6 / G2 | **proved**: decoded JALR enters the actual loaded, aligned callee with the allocator return link and both native save frames; shared indirect adapter preserves the full call interface; free-list body, allocation/header/accounting and return **open** |
| Best-fit exact-size small-list allocation | `BestFitSmall.lean:allocate`, `Post.head`, `Post.counter_nat` | A6 / G2 | **proved**: actual function entry through return for nonnull head/tail and unchanged merge cursor; exact head/accounting stores and returned header pointer; counter does not wrap under free-word credit; other branches and full free-list invariant preservation **open** |
| Best-fit merge-cursor repair and nonempty-tail coverage | `BestFitRepair.lean:allocate_nonempty`, `allocate_repair`, `RepairPost.cursor` | A6 / G2 | **proved**: initial memory selects either merge-cursor branch, both execute through native return with exact effects; repaired cursor points to the list-head cell; empty-successor bitmap update and remaining allocator branches **open** |
| Best-fit empty-tail bitmap/accounting/return suffix | `BestFitBitmapReturn.lean:clear_return`, `BestFitBitmap.lean:cleared_word`, `BestFitFinish.lean:finish` | A6 / G2 | **proved**: actual LW/SLLW/AND/SW clears the selected size-class bit, shared accounting suffix returns the header pointer and frames code/native/output; empty-tail entry/pop composition and other allocator branches **open** |
| Complete best-fit exact-size small-list allocation | `BestFitExact.lean:allocate`, `Post.counter_nat`, `BestFitEmpty.lean:allocate` | A6 / G2 | **proved**: all four cursor/successor combinations execute from actual function entry through native return; memory determines branches, exact effects/accounting and native/code/output frames retained; larger-size search/splitting, large tree, and full free-list invariant preservation **open** |
| Free-block split, both remnant-size branches | `BestFitSplit.lean:split`, `BestFitSplitGeometry.lean:Post.remnant` | A6 / G2 | **proved**: actual `bf_split` entry through native return, memory-selected branch, exact accounting/remnant-header stores and carved header address; decoded remnant size/tag and final-memory readback proved; free-list ownership and allocator caller composition **open** |
| Minor-allocation accounting and native return | `AllocAccountReturn.lean:account_return`, `ReturnPost.result`, `ReturnPost.header`, `ReturnPost.counter_nat` | A6 / G2 | **proved**: actual header store/accounting/epilogue on no-major-slice route, exact memory and restored save-bank observations; color selection, free-list call composition and major-slice request **open** |
| Successful minor-allocation continuation, all colors | `AllocSuccess.lean:finish`, `Post.result`, `Post.header` | A6 / G2 | **proved**: nonnull free-list return through real saved-tag/phase/sweep selection, header construction, accounting and native return on no-major-slice route; exact effects, final header size/tag and native/output frame; free-list call composition and major-slice request **open** |
| Exact-size free-list entry through allocating-wrapper return | `AllocExact.lean:allocate`, `BestFitExact.effect_high` | A6 / G2 | **proved**: all exact-size small-list cases and all successful color routes compose through actual native return; exact combined effects, payload result and native/output frame; prologue/JALR and caller save-bank composition **open** |
| Complete exact-size allocating wrapper | `AllocWrapper.lean:allocate`, `Post.header`, `SaveBank.read` | A6 / G2 | **proved**: actual prologue, loaded JALR, all exact-size branches and successful colors through original caller return; original save-bank restoration, exact memory, payload and typed header; fresh-oldify composition, other allocator routes and major-slice request **open** |
| Fresh oldify through exact-size allocation | `FreshAllocated.lean:allocate_fresh`, `AllocationFootprint.lean` | A6 / G2 | **proved**: actual oldify entry and allocating call return to forwarding/queue code with payload/source pins, exact effects and code/native/output frame; queue insertion/return composition, larger-size/tree routes and collector closure **open** |
| Complete fresh large scanned-object queue route | `FreshEnqueued.lean:enqueue_fresh`, `Enqueued.payload` | A6 / G2 | **proved**: actual oldify entry, exact-size allocation, root/forwarding updates, queue insertion and original native return; represented grey payload via shared Eqv transport; heap/stack geometry suppliers, other object/allocator routes and collector closure **open** |
| Typed header after complete fresh queue route | `FreshHeader.lean:Enqueued.header_nat` | A6 / G2 | **proved**: original size/tag survive allocation, accounting and queue writes under explicit counter/queue separation; address normalization derives from allocator RAM geometry |
| Zero small-bitmap helper return | `FfsZero.lean:zero`, `Generated/FfsZero.lean` | A6 / G2 | **proved**: actual `ffs(0)` native return, zero result, unchanged memory and register/output frame; empty-small-list caller prefix and large-block fallback composition **open** |
| Empty-list allocator entry through bitmap search | `BestFitMissing.lean:missing_search_zero`, `BestFitFallback.lean` | A6 / G2 | **proved**: real entry size/list tests, bitmap filter, decoded native saves, linking ffs call and zero-result return; total reads and exact memory/native/output effects; large-block continuation and nonzero bitmap search **open** |
| Least-large-block test and actual split call | `BestFitLarge.lean:prepare`, `split` | A6 / G2 | **proved**: saved-size reload, nonnull least-block and actual size tests, native saves, linking `bf_split` call and return; carved-header result, exact combined stores and native/code/output frame; bitmap-prefix composition and final accounting/native return **open** |
| Allocator entry through least-large-block split | `BestFitFallbackLarge.lean:missing_large_split`, `SaveBank.Shape.read` | A6 / G2 | **proved**: actual empty-list/bitmap path and large-block split compose from allocator entry; saved-bank readback, initial-snapshot geometry, exact effects and code/native/output frame; final accounting/native return **open** |
| Complete least-large-block allocator alternative | `BestFitLargeComplete.lean:allocate_large`, `Allocated.requested` | A6 / G2 | **proved**: actual entry, empty-list/zero-bitmap search, least-block split, free-word accounting and original native caller/stack return; original request readback, exact effects and code/native/output frame; wrapper composition and other allocator routes **open** |
| NoForgery / remembered completeness / writing-arm barrier interface | `OCaml/Vm/Gc/Invariant.lean` | A6 / a1-arms | named `LoopHead` and `WritingArmBarrier`; `LoopHead.reloc` and empty-table reset rule **proved conditionally**; concrete table linkage, startup and arm suppliers open |
| Remembered-set logical store rule | `OCaml/Vm/Gc/Barrier.lean` | A6 / a1-arms | `slotComplete_store`, `rememberedComplete_of_slots` **proved**; machine caml_modify, concrete table linkage and major darkening remain open |
| Candidate live-word budget | `OCaml/Vm/Gc/Budget.lean` | A6 | `liveWords_le_allocated`, `fitsLive_of_fits` **proved**; production `Fits` unchanged pending GC/reclamation proof |
| symbolic heap allocation/read laws; arbitrary-heap closure capture/read segment | `OCaml/Logic/Symbolic.lean` | B′1 | **proved** (`Heap.get_alloc_old`, `Heap.get_alloc_fresh`, `field_alloc_fresh`, `field_alloc_old`, `closure_capture_read`) |
| absolute-address code locality (`decodeAt_extract`, `CodeSlice.iter_eq`) | `OCaml/Logic/CodeSlice.lean`, `OCaml/Run/Local.lean` | B′1 | **proved**, instantiated by `CertifiedBlock.run` and all generated windows |
| bytecode decode table / segment generators for `boot/ocamlc` | `scripts/gen_bc_rules.py`, `OCaml/Programs/Generated/` | B′1 | **done**: 23,678 instructions / 5,414 block rules, four modules build at default heartbeats; measurements in `results/bprime_build.json` |
| push/enter, over/under-application boundaries and application-summary composition | `OCaml/Logic/Application.lean`, `ApplicationSteps.lean` | B′1 | **proved** (`apply1_enter`, `return_over`, `grab_under`, `restart_partial`, `call_summary`, `tail_summary`) |
| generated function summary → MachWP → `bytecode_adequacy` | `OCaml/Programs/GeneratedAdequacy.lean` | B′ exit | **proved** (`jumpStop_adequacy`, small branch-function fixture) |
| `OCamlSem` on Lambda (LLM-written) + its program logic | new `OCaml/Source/Sem.lean` | C1 | open |
| **`ocamlc_backend_correct_Statement`** (Bytegen/Emitcode, then Translcore/Matching) | `OCaml/Theorems.lean` | C2 | open |
| `BackendCorrectFor` the compiler's own build | `OCaml/EndToEnd.lean` | C2 | open |
| **`boot_ocamlc_fixpoint_Statement`** (one translation validation) | `OCaml/Theorems.lean` | C3 | open |
| `EndToEndMachine` (run `boot/ocamlc` on the machine, files in `WorldRepr`) | `OCaml/EndToEnd.lean` | E | open |

## P0: validation and scaffold (done)

* **Result** (VALIDATION.md): the ELF runs on Sail (`while.ml`,
  9 difftests, `boot/ocamlc -version`, `boot/ocamlc` compiling a one-line
  program); census of the ELF and of `boot/ocamlc`; `BcSem` agrees with the
  host `ocamlrun` on the F1 programs (compiled evaluation) and with the ELF
  on `while_min` (kernel evaluation); `boot/ocamlc` is a fixpoint of the
  4.14.4 sources up to configuration strings.
* **Scaffold**: ZINC syntax and decoding (`Opcode.lean` generated), `BcSem`
  F1, fragment ledger, `VmReprAt`/`VmRepr` (placement-existential),
  `Loaded`, statements of all layers, the proved compositions.
* **Exit**: `scripts/check_all.sh` passes.

## A0: retarget the machine layer (exit: `Loaded` has a witness)

**Startup status (lane a0-boot):** `runtimeLayout freeList` now permits a
nonempty nursery, as authorized by the foreman. At the measured `while_min`
cut (step 4,269,257), `young_ptr = 0x80281ce0` and
`young_alloc_end = 0x80282000`: 800 nursery bytes remain allocated.
`startup_byt.c` promotes globals without resetting the nursery, then
`caml_sys_init` allocates argv. The small projection checks are
kernel-checked; the reachable Sail-state certificate is still open.

**One runtime image:** program bytes, argv and environment are in a fixed
`.embed` section. The while/while_min/compiler images have identical
`.text`, `.rodata`, `.data` and `.tohost`, so all use one generated Layout
and the same A0 library code facts. The migration regenerates decode tables,
library layouts/pins/specifications, arm pilots and OCaml image pins. The
complete cut is freshly captured and compared against every native memory
byte and register. `WhileMin.loaded_fillZero` is a closed kernel theorem
for that snapshot; it does not assert kernel startup reachability.

* Done in P0: the 66 byte-identical library functions (`scripts/retarget_syi.py`).

* Instantiate `Layout.runtimeOk` with the collector's invariants at the cut
  point (minor heap bounds, `young_alloc_start ≤ young_ptr ≤ young_alloc_end`,
  `caml_something_to_do = 0`, free-list shape as an abstract predicate).
  The allocated nursery interval is ordinary represented heap.
* Regenerate the decode table, code lemmas and image pins for
  `c/ocamlrun-riscv-htif.elf` (`experiments/syi/gen_decode_table.py`,
  `gen_code_lemmas.py`); regenerate the 130 identical library functions'
  site proofs at their new addresses (done for the 66 byte-identical ones);
  regenerate `strcmp`/`__ssprint_r`/`__ssputs_r` (8 changed words) and
  `_malloc_r`/`_free_r`/`_svfprintf_r` (code differs); replace per-word
  decode lemmas by ship-your-interpreter's `decodeW`.
* Boot witness for `while_min` (4.27M steps to the cut) with
  `scripts/syi/gen_boot_witness.py`.
* **Exit**: `Loaded L whileMin (fillZero c)` for the machine's own entry
  state, kernel-checked; `#print axioms` standard.

## A1: F1 arms (exit: `ocamlrun_refinement_Statement` for F1)

**Repaired contract:** `Running L P s c` has separate `data : VmRepr`,
`platform : PlatformOk L.runtimeOk`, and `loop : LoopRegisters` fields.
`PlatformOk` requires Sail `GoodState` (including `htif_done = false`),
exact OCaml ELF `.text`/`.rodata` pins, and `L.runtimeOk`. Fixed dispatch
registers are extracted by `gen_layout.py`; variable VM registers remain
in the data representation. `LoadedAt.platform` is A0's entry obligation;
the interpreter prologue must establish the loop registers. The `ArmSim`
entry/next/halt fields and `run_sim` carry `Running` throughout.
`OcamlrunRefinement` itself is unchanged.

The old counterexample remains checked against `DataOnlyArmSim` in
`OCaml/Vm/Sim/Obstruction.lean`; `forceExit_not_running` excludes it from
the repaired relation. `PlatformReloc.lean` supplies `Eqv` atoms and
transport for platform/image frames and fixed loop registers. Actual
collector control/runtime restoration remains an explicit obligation.
The generated CONST0/NEGINT/ISINT/ACC0/ACC body theorems preserve positive
run counts via `TripleN` (3/4/5/3/6), using the existing run-counter law.
Their `StepFrameOut` postconditions preserve console and all registers
outside the generated write log using `chain_frame_out`.
The exact OCaml image literals are generated by `gen_ocaml_image.py` and
gated for drift; the copied WHILE `FixedImage` bytes are not used as pins.
A0 library projections can consume the shared `FixedBytesLoaded` interface.

* One segment family per F1 arm (median 7 instructions), generated by
  `disasm_to_segment.py` → `gen_segment.py`, with the new site classes
  (tagged-int ALU, `slli`/`srai`/`addw`), the dispatch lemma (jump table)
  and the allocation fast path. Primitives: `gen_fn.py` summaries for the
  30 F1 primitives against `primF1Impl`, owned by lane **a1-prims**.
  C_CALL arms consume named call-site/return-state summary premises until
  those machine summaries land; their prefix/suffix composition stays in A1.
* Budget: G1 (PLAN §GC) — `Fits` with the minor heap as the heap budget;
  the slow path is excluded by `Fits`.
* **Exit**: `ArmSim L B P` for every `P`; hence
  `ocamlrun_refinement_Statement L B` by `ocamlrun_refinement_of_arms`;
  instantiated on `whileMin` with `whileMin_bcSem` gives
  `Halts c "55\n2500\n36\n" 0` for the machine. Also: a chunked
  kernel-checked `BcSem` run of the Stdlib-linked `while.ml`.

## A2–A5: F2 data, F3 objects, F4 callbacks, F5 files

Semantics-lane exit: **9/9 host/runbc difftests pass**
(`results/bc-f2-f5.json`), plus focused data, formatting/float and file tests
(`results/bc-focused.json`). The successful boot/ocamlc hello compilation
census has 121 opcode kinds and 86 primitive names; kernel-checked
`executed_opcodes_ledgered` and `executed_primitives_ledgered` cover every
measured name. The measurement is host evidence, not a BcSem compiler run.

| Semantics slice | Current status / remaining boundary |
|---|---|
| F2 data | Ten opcode arms; data/format/float/boxed-integer subsets. Bytes carry initialization state: observations require initialized cells and relocation constrains only known payload bytes. All 86 measured compiler primitives have executable domains; `primitiveOpen = []`. Compiler differential matches both `.cmo`/`.cmi` bytes and output, with 16 explicit host GC snapshots. `GcObservationInput` is the remaining machine observation premise; universal primitive refinement remains open. |
| F3 objects | Object/method semantics validated; `CodeWordOk` relaxes only linearly decoded GETPUBMET cache slots. Cache hit/miss simulation and method-table invariants remain open. |
| F4 callbacks | Re-entrant one/two/three/N callbacks, `_exn` returns and uncaught handlers/printers/fallback are implemented; seven host/C-runtime differentials pass. Saved frames and pending exceptions are roots. Disabled backtraces are supported; active backtraces, signals, finalisers and machine simulation remain open. |
| F5 files | World uses `TCB.Os.OsState`; buffered file/env/time primitives use `osCall_sound`. ELF entry classification and candidate `HtifMemoryAt` relation are concrete (RV64-measured Layout). ABI decoders, startup establishment and ELF function proofs remain open. A seven-call trace exposes 256-byte names skipped by readdir; `longName_eof_rejected`/`longName_not_special` check the spec obstruction. |
| Executable heap | Array-backed storage with certified list-view compilation (`Heap.get?_eq_getArray`); existing symbolic heap/application proofs retained. |

`docs/lanes/a2-sem.md` records argument-domain restrictions, proof boundaries
and the image-migration regeneration requirement. Machine arms remain a1's
work; passing executable difftests does not discharge Layer A.

* Each fragment: its `BcSem` rules and primitives (grown in
  `Semantics.lean`, validated with `runbc` against the host `ocamlrun`
  on its difftests before any proof), its arms, its primitive summaries.
* F3 relaxes `VmReprAt.code` to "code up to method caches"
  (`GETPUBMET` writes into the code).
* F4 nests the simulation for re-entrant `caml_interprete` (callbacks).
* F5 moves `BcSem`'s world to `TCB.Os.OsState`, specifies the file, time
  and environment primitives through `OsStep`, adds the file system to
  `WorldRepr`, and discharges `HtifFsImplements` (`htif.c` already passes
  the spec's trace validation: 6,410 accepted, 0 rejected).
* **Exit per fragment**: the difftests of the fragment pass under `runbc`
  and on Sail, and Layer A holds for the fragment.

## A6: the collector (exit: Layer A without the G1 budget)

* Round 2: Kiran chose observational `GcSafe` beside unchanged `Good` and
  `Fits`; BcSem stays deterministic. Forward edits cover roots and heap
  fields independently, under minor_gc.c's payload-tag guard. `GcReach`
  includes prior collection edits. Safety compares halt code/console and
  divergence at conservative collection boundaries, not intermediate-step
  lockstep. Boundary completeness is a named machine-proof obligation.
* `GcSafe boot/ocamlc` is open. The host compiler comparison passes at
  default and small minor heaps; the static observation scan is deliberately
  conservative and does not certify lazy-flow reachability. Typed OCaml can
  observe lazies with physical equality without Obj: the host regression
  prints `false true` across collection. The real CamlinternalLazy.force
  bytecode proof establishes convergence of Forward and payload calls in
  twelve/fourteen steps (`force_observations`); it is not a typing theorem.
* G2: the minor collection preserves `VmReprAt` up to a new placement
  (oldify/mopup + remembered set); the major heap is non-moving and
  sweeps only non-`Live` blocks; compaction off (`O=1000000`).
* Route (adopted, round 1): every `VmReprAt` component as an `Eqv` term
  (`OCaml/Vm/Reloc.lean`; done: value words, objects, stack, `HeapRepr`,
  globals, registers, code, domain fields, channels/world: `vmReprAt_reloc`). The collector simulation must supply `ScanCoherent`, plus the
  premises the L3′ check found (`abstractions/ROUND-1.md` §2):
  * NoForgery: no scanned word looks young unless it is a young pointer;
  * RememberedComplete: every old→young field is in `ref_table`,
    maintained by `caml_modify`;
  * a lax clause for `Forward_tag` short-circuiting;
  * interior pointers only behind `Infix_tag`.
* Law checks now include 42 `Forward_tag` cases and 12 valid infix cases
  (`abstractions/round1/check_laws.py`). Strict object preservation fails
  for short-circuiting Forward blocks; arbitrary interior pointers fail
  without an Infix header. `Forward.lean` checks the strict bridge obstruction
  and shows a transparent value relation does not preserve ISINT on all
  abstract values. The pinned host 4.14.4 regression reproduces it.
* Header images preserve tag/size and allow promotion recoloring; raw
  payload images cover exactly Wosize words (`headerView_color`,
  `payload_copyIn`, `ObjMoved`).
* `LoopHead` adds named NoForgery, RememberedComplete and InfixValid fields;
  `WritingArmBarrier` records the a1 supplier obligations. Concrete runtime
  ref-table linkage and use in the production ArmSim remain open.
* `FitsLive` and `fitsLive_of_fits` are checked candidate budget facts,
  not a discharge of G2 or a replacement for production `Fits`.
* `scripts/gc_cfg.py --check` records gen_fn's coverage: oldify is 145
  instructions / 38 blocks, without a recognised counted-loop template;
  mopup exceeds the branch limit, empty-minor-heap the instruction limit.
  The generic `Vsa.Sim.DeriveCaseRow` adapter (`segToTriple`) is now ported
  and checked. `scripts/gen_gc_rows.py` generates oldify-one and caml_modify
  segments with code pins; their 387 declarations are audited by
  `#audit_gc_rows`. Register results and execution bookkeeping are retained
  in named-field posts. Call summaries and the oldify/mopup loop invariants
  remain open.
* **Exit**: `Fits` restated on live words; `ocamlc` compiling a one-line
  program is within Layer A.

## B′: the exponentiating layer on bytecode

* `scripts/gen_bc_rules.py` reads host 4.14.4 `dumpobj` and cross-checks all
  instruction boundaries/opcodes against CODE. It emits 5,414 symbolic-window
  run rules over all 23,678 instructions of Translcore, Matching, Bytegen and
  Emitcode, grouped into 585 closure-entry regions. Calls and control-flow
  targets split blocks; straight-line windows are capped at 16 instructions.
* Route: symbolic reduction of real `stepI`, allocation/read laws in
  `Symbolic.lean`, and `loop_rule`. Run laws come from `OCaml/Run/`.
  `decodeAt_extract`, `CodeSlice.iter_eq`, and `CertifiedBlock.run` preserve
  absolute PCs while evaluating small windows. Generated rules take an exact
  extracted-code pin and a successful local symbolic run; they do not assume
  an unproved full-program run. Unsupported instructions retain their real
  unsupported outcome.
* Calls: `ApplicationSummary` retains the extra-argument count and caller
  frame; `call_summary`/`tail_summary` compose runs. `apply1_enter`,
  `return_over`, `grab_under`, `restart_partial` prove the push/enter and
  arity-mismatch boundaries. Client function invariants, postconditions and
  termination remain program-proof obligations.
* Scale: all four generated modules build at default heartbeats under 24 GiB.
  Translcore 75.33 s / 1.44 GiB, Matching 243.75 s / 3.06 GiB,
  Bytegen 235.05 s / 1.50 GiB, Emitcode 38.55 s / 0.94 GiB peak RSS.
  `results/bprime_build.json` records CPU time and source hashes too;
  `scripts/measure_bc_rules.py` reproduces the measurements sequentially.
  Stage a5 checks generator drift and all 5,414 generated theorem axiom sets.
* **Exit discharged**: generated rules for all 23,678 back-half instructions
  build within the budget. `jumpStop_adequacy` instantiates
  `bytecode_adequacy` end to end via a generated branch-function summary,
  `MachWP.run` and `MachWP.haltConsole`, with proved initial ownership and WP.
  The fixture is deliberately small; compiler correctness remains Layer C.
  `bcModel.ok` bounds the natural PC by 2^64 so its ghost register cannot alias
  another address (`pc_alias_excluded`).

## C1–C3: the compiler at the source level

* C1: `OCamlSem` on Lambda (LLM-written), its WP and adequacy; validated
  by running it (executable) against the host `ocaml` toplevel on the
  difftests.
* C2: `ocamlc_backend_correct_Statement` for Bytegen/Emitcode, then
  Translcore/Matching; `BackendCorrectFor` the compiler's build.
* C3: `boot_ocamlc_fixpoint_Statement`: `boot/ocamlc`'s CODE equals the
  verified backend's output on the compiler's Lambda (trusted front end),
  DATA up to the configuration strings (VALIDATION §Fixpoint).
* **Exit**: `endToEnd_ocaml_Statement` by `endToEnd_of_layers`.

## E: on the machine

* `EndToEndMachine`: `boot/ocamlc` itself runs under Layer A (F1–F5 + GC)
  on the machine and writes `/out/a.out` into the in-memory file system.

Collector observations: `OCaml/Vm/GcObservation.lean` defines `GcSnapshotAt`
and `GcObservationInput` at the C entry using generated Layout symbols and
Caml_state offsets. The compiler differential supplies 16 observations from
a host linker wrapper and checks unchanged host artifacts. This does not
discharge their correspondence to the pinned ELF's collector.
