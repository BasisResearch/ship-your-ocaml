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
| `HtifFsImplements` (the in-image file system meets the OS spec) | `OCaml/Os.lean` | F5 | reduced by `htifFsImplements_of_functions` to `HtifEntries` + `HtifFunctionObligations` (termination/partial correctness); premises open. Native trace evidence: 6,410 accepted, 80 special, zero rejected (`results/htif-fs.json`) |
| `BcSem` world over `TCB.Os.OsState` (file/time/env primitives through `OsStep`) | `OCaml/Bytecode/Semantics.lean` | F5 | open |
| Linux instantiation: `ecall` as an external step constrained by `OsStep` | `Vsa.Machine` extension | E | open |
| `Layout.runtimeOk` concrete instance | `OCaml/Vm/Runtime.lean` | A0 | **defined**: `runtimeLayout freeList`, with ordinary nonempty-nursery bounds |
| `Loaded` at real entry states (boot witnesses, small programs) | `OCaml/Vm/Boot/` | A0 | **proved for the complete captured while_min cut**: `WhileMin.loaded_fillZero`, no premises; full native-state comparison; kernel reset-to-cut execution remains open |
| `WhileMinObservation.bounds`, `noPending`, `nursery_not_empty` | `OCaml/Vm/Boot/WhileMinObservation.lean` | A0 | **proved for the observed projection**; complete native capture validates it; kernel startup execution remains open |
| `WhileMinLog.logOk`, `memory_view` | `OCaml/Vm/Boot/WhileMinLogChecks.lean` | A0 | **proved**: exact memory effect of 35,304 observed stores, checked in small chunks; kernel Sail execution remains open; closed `Loaded` now proved separately |
| `WhileMinRuntime.runtimeOk`, `runtimeOk_fillZero` | `OCaml/Vm/Boot/WhileMinRuntime.lean` | A0 | **proved for the certified memory candidate**: nursery bounds, no pending work and singleton best-fit free-list shape; actual startup execution remains open |
| `WhileMinHeap.repr`, `WhileMinEntry.code`, `loaded_fillZero` | `OCaml/Vm/Boot/WhileMin{Heap,Entry}.lean` | A0 | **proved**: all 29 objects, non-overlap, closure, 191 code words and runtime assembled; `WhileMin.loaded_fillZero` discharges memory, control/image and all 403 primitive bindings for the complete capture |
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
| `addint_step_arm`, `subint_step_arm`, `andint_step_arm`, `orint_step_arm`, `xorint_step_arm` | `OCaml/Vm/Sim/*int.lean`, `StackConsume.lean`, `ReadOnly.lean` | A1 | **proved conditionally**; one generated integer-binary family, shared stack/root restoration and semantic input extraction; dispatch/runtime frame/read geometry remain explicit |
| `lslint_step_arm`, `lsrint_step_arm`, `asrint_step_arm`, `shift_count` | `OCaml/Vm/Sim/*int.lean`, `ShiftArithmetic.lean` | A1 | **proved conditionally**; shared six-bit native count, full-domain tagged results and successful-step wrappers, reusing binary restoration |
| `ltint_step_arm`, `leint_step_arm`, `gtint_step_arm`, `geint_step_arm`, `ultint_step_arm`, `ugeint_step_arm` | `OCaml/Vm/Sim/*int.lean`, `ComparisonArithmetic.lean` | A1 | **proved conditionally**; both native branch paths of all six signed/unsigned integer comparisons, sharing the binary generator and stack restoration |
| `tr_isint`, `isint_loaded` (generated five-instruction machine body with SLLI/ANDI) | `OCaml/Vm/Sim/Isint*.lean` | A1 | **proved**; full representation/frame bridge open |
| `isint_arm`, `isintWord_repr`, `isint_not_valWord` | `OCaml/Vm/Sim/Isint*.lean` | A1 | **proved conditionally** on dispatch readiness, runtime frame, even placement and non-raw accumulator; checked value-level alignment obstruction retained |
| `tr_negint`, `negint_loaded` (generated four-instruction tagged-negation body) | `OCaml/Vm/Sim/Negint*.lean` | A1 | **proved**; represented composition below |
| `negint_arm`, `immediate_restore`, `tag_neg`, `untag_neg` | `OCaml/Vm/Sim/Negint.lean`, `Immediate*.lean` | A1 | **proved conditionally** on `ArmInput` / runtime memory frame, with exact modular `stepI` result |
| `tr_offsetint`, `offsetint_width_obstruction` | `OCaml/Vm/Sim/Offsetint*.lean`, `OffsetWidth.lean` | A1 / A2 semantics | **body and obstruction proved**; host/runbc disagree at operand 2^30 because ELF uses SLLIW and stepI shifts 64 bits; OFFSETINT/OFFSETREF semantics correction required |
| `boolnot_arm`, `tag_sub`, `tag_not` | `OCaml/Vm/Sim/Boolnot*.lean`, `ImmediateArithmetic.lean` | A1 | **proved conditionally**; NEGINT/BOOLNOT generated from one shared tagged-subtraction bridge, for all 63-bit integer inputs |
| `tr_acc0`, `tr_acc`, `acc0_loaded`, `acc_loaded` (generated stack loads through total RAM reads) | `OCaml/Vm/Sim/Acc*.lean` | A1 | **proved**; address geometry and representation/frame bridge open |
| `acc0_arm`–`acc7_arm`, `accu_restore`, `accu_arm`, `stack_slot_nat` | `OCaml/Vm/Sim/Acc*.lean`, `StackAcc.lean`, `Immediate.lean` | A1 | **proved conditionally**; one generated stack-load family, shared live-root restoration, non-wrapping addresses derived from representation; RAM/HTIF windows explicit |
| `envacc1_arm`–`envacc4_arm`, `getfield0_arm`–`getfield3_arm`, `FieldSelection.read`, `RamReadAt.window` | `OCaml/Vm/Sim/Envacc*.lean`, `Getfield*.lean`, `FieldRead.lean`, `ReadGeometry.lean` | A1 | **proved conditionally**; one generated field-load family, represented lookup/root witnesses derived; RAM/HTIF geometry explicit |
| F1 primitive summaries (`primsF1`, 30 entries) | `OCaml/Vm/Primitives/` | A1 | **16/30 proved**: system constants, signed integer comparison, argv, string/bytes lengths, fresh object IDs and canonical string equality/inequality, generated ELF `FnSummary` plus represented VM payload/result and platform/ABI frame; read-only runtime preservation uses `MemoryStable` (proved for `RuntimeOk` from its free-list frame law); counter/native-stack writes use `WindowStable` plus separation. Other 14 primitives open |
| Nursery allocation support | `OCaml/Vm/Primitives/Allocation.lean`, `DoubleFast.lean`, `DoubleLayout.lean` | A1 | Heap extension and `caml_copy_double` successful nursery path proved from generated block certificates; collector path and primitive tail bridge open, not counted toward 30 |
| `tr_dispatch`, `dispatch_loaded` (in-range dispatch machine path) | `OCaml/Vm/Sim/Dispatch*.lean` | A1 | **proved**; Running/jump-table-to-arm bridge open |
| `dispatchOffset_loaded`, `dispatchOffset_target`, opcode guard/target geometry | `OCaml/Vm/Sim/DispatchTable*.lean` | A1 | **proved** for all 149 pinned table entries; dispatch composition open |
| `dispatch_run` (named dispatch-to-arm boundary and complete frame) | `OCaml/Vm/Sim/Dispatch.lean` | A1 | **proved**; bytecode RAM/HTIF geometry and tick premises remain explicit |
| F2/F3/F4/F5 arms and primitives | `OCaml/Vm/Sim/` | A2–A5 | open |
| GC: `caml_empty_minor_heap` preserves `VmReprAt` up to a new placement (G2) | `OCaml/Vm/Gc/` | A6 | open: strict Forward bridge obstructed; machine oldify/mopup proof remains open |
| Forward short-circuit obstruction / transparent-value ISINT incompatibility | `OCaml/Vm/Gc/Forward.lean` | A6 | **proved**; pinned host regression confirms `false true`; semantic safety precondition or revised semantics needs a decision |
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
| F2 data | Ten opcode arms; data/format/float/boxed-integer subsets. Primitive domains and eleven remaining compiler boundaries are explicit in `Fragment.lean`; universal primitive refinement remains open. |
| F3 objects | Object/method semantics validated; `CodeWordOk` relaxes only linearly decoded GETPUBMET cache slots. Cache hit/miss simulation and method-table invariants remain open. |
| F4 callbacks | Caught exceptions and disabled-backtrace primitives validated. Re-entrant callbacks, uncaught exceptions, signals and finalisers remain open; the nine-test exit does not certify them. |
| F5 files | World uses `TCB.Os.OsState`; buffered file/env/time primitives use `osCall_sound`. HTIF reduced to named typed function premises with trace evidence; concrete FS memory relation and ELF function proofs remain open. |
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
