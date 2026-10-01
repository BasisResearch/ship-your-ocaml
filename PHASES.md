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
| relocation invariance of value words, objects, stack, `HeapRepr`, globals (`Eqv` combinators) | `OCaml/Vm/Reloc.lean` | round 1 (A6 route) | **proved** under the typed relocation; the real-collector bridge `ScanCoherent` is open (A6) |
| symbolic stepping + `loop_rule`; a counting loop for any bound | `OCaml/Logic/Symbolic.lean`, `OCaml/Programs/CountLoop.lean` | round 1 (B′ route) | **proved** |
| OS spec (SibylFS + CakeML port), executable checker `allowed_sound`/`allowed_complete`/`checkTrace_sound` | `tcb/TCB/Os/` | P0 | **proved**; spec **trusted** for Linux, validated on 6,490 Linux traces (0 rejected) |
| library proofs of the 66 byte-identical functions retargeted to this ELF | `Vsa/`, `scripts/retarget_syi.py` | P0 | **done** (pins checked, `memcpy_bytepath_spec`/`muldi3_spec`/`udivdi3_spec` audited) |
| `strcmp_full_spec_cond` for this ELF (aligned and unaligned ASCII C strings, framed return) | `Vsa/Sim/StrcmpSpecCond.lean` | A0 | **proved**, regenerated address/mask retarget, pinned and audited |
| `ssputs_fast_spec` and `ssprint_iov2_spec` for this ELF (short disjoint copies, sufficient capacity, two iovecs) | `Vsa/Sim/SnprintfSpec19.lean`, `SnprintfSpec20Part4.lean` | A0 | **proved**, retargeted call/region addresses, pinned and audited; framed return and copied bytes |
| Allocator symbolic-run soundness and regenerated instruction table | `VsaIris/Vsa/SymRun.lean`, `AllocSteps/Part*.lean` | A0 | **proved**: 1,459 instruction-step lemmas, including all `_malloc_r` and `_free_r` words; generic SWP soundness and representative entry sites audited; a5 drift check |
| Allocator heap geometry, sbrk and checked malloc paths | `VsaIris/Vsa/{HeapTake,HeapFree,MallocPaths,MallocExtend}.lean` | A0 | **proved**: relocated bin/global geometry, split/coalesce/frame preservation, `_sbrk_r`, small/remainder/top/growth paths; 37-module generated closure, headline audits and a5 drift check |
| `_malloc_r` and `malloc` function contracts for this ELF | `VsaIris/Vsa/MallocBlocks2.lean`, `MallocRunAll.lean` | A0 | **proved**: `malloc_all` at `_malloc_r` entry, plus `mallocChgRun_proved` and `mallocLocalRun_proved`; complete generated step/pin closure, audited |
| `_free_r`, `_svfprintf_r` function specs for this ELF | `experiments/syi/while-elf-only/` → `Vsa/` | A0 | open; complete code regions pinned and decoded; changed-layout run compositions still being ported |
| decode for every disassembled instruction word (via syi’s `decodeW`) | `Vsa/Sim/ElfDecode/`, `scripts/gen_elf_decode.py` | A0 | **proved**: 29,475 words, 231 chunks; covers all reachable words; a5 drift check |
| `HtifFsImplements` (the in-image file system meets the OS spec) | `OCaml/Os.lean` | F5 | open; `htif.c` conforms on all 6,490 validation scripts (VALIDATION §6) |
| `BcSem` world over `TCB.Os.OsState` (file/time/env primitives through `OsStep`) | `OCaml/Bytecode/Semantics.lean` | F5 | open |
| Linux instantiation: `ecall` as an external step constrained by `OsStep` | `Vsa.Machine` extension | E | open |
| `Layout.runtimeOk` concrete instance | `OCaml/Vm/Runtime.lean` | A0 | **defined**: `runtimeLayout freeList`, with ordinary nonempty-nursery bounds |
| `Loaded` at real entry states (boot witnesses, small programs) | `OCaml/Vm/Boot/` | A0 | **open, stopped on ELF text mismatch**: 7,484 bytes / 5,954 words differ; execution/projection certificate remains open |
| `WhileMinObservation.bounds`, `noPending`, `nursery_not_empty` | `OCaml/Vm/Boot/WhileMinObservation.lean` | A0 | **proved for the observed projection**; machine-to-projection certificate remains open |
| `ArmSim` entry + F1 arms (134 opcodes) + halt | `OCaml/Vm/Sim/` | A1 | open; strengthened `Running` contract excludes the HTIF obstruction |
| **`ocamlrun_refinement_Statement L B`** (Layer A, F1) | `OCaml/Theorems.lean` | A1 (by `ocamlrun_refinement_of_arms`) | open; derives unchanged from the repaired arm contract |
| `PlatformOk`, `Running`, `forceExit_not_running`, `platformOk_reloc`, `loopRegisters_reloc` | `OCaml/Vm/Platform*.lean`, `OCaml/Refinement.lean` | A1 | **contract repaired**; composition and regression/transport theorems proved |
| `repr_forceExit`, `armSim_not_repr`, `loaded_not_armSim` | `OCaml/Vm/Sim/Obstruction.lean` | A1 | **proved** against legacy `DataOnlyArmSim`; retained as a regression witness |
| `tr_const0`, `const0_loaded` (first generated machine arm body and full-image pin projection) | `OCaml/Vm/Sim/Const0*.lean` | A1 | **proved**; dispatch and full representation/frame bridge open |
| `tr_isint`, `isint_loaded` (generated five-instruction machine body with SLLI/ANDI) | `OCaml/Vm/Sim/Isint*.lean` | A1 | **proved**; full representation/frame bridge open |
| F2/F3/F4/F5 arms and primitives | `OCaml/Vm/Sim/` | A2–A5 | open |
| GC: `caml_empty_minor_heap` preserves `VmReprAt` up to a new placement (G2) | new `OCaml/Vm/Gc/` | A6 | open |
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
cut (step 4,269,235), `young_ptr = 0x80283ce0` and
`young_alloc_end = 0x80284000`: 800 nursery bytes remain allocated.
`startup_byt.c` promotes globals without resetting the nursery, then
`caml_sys_init` allocates argv. The small projection checks are
kernel-checked; the reachable Sail-state certificate is still open.

**ELF stop:** `scripts/check_boot_text.py` and
`results/boot/while_min-text.json` record 7,484 differing `.text` bytes
across 5,954 instruction words between the pinned proof ELF and the
standalone `while_min` ELF. Do not reuse a0-lib code/decode facts for that
ELF. The second-layout path is stopped per the foreman's instruction;
the pinned ELF is unchanged. `OCaml.Layout` currently parameterizes only
`runtimeOk`, while representation addresses are global generated constants.
The fallback is to move embedded program data after BSS, with approval
before replacing the pinned ELF. See `docs/lanes/a0-boot.md`.

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
The exact OCaml image literals are generated by `gen_ocaml_image.py` and
gated for drift; the copied WHILE `FixedImage` bytes are not used as pins.
A0 library projections can consume the shared `FixedBytesLoaded` interface.

* One segment family per F1 arm (median 7 instructions), generated by
  `disasm_to_segment.py` → `gen_segment.py`, with the new site classes
  (tagged-int ALU, `slli`/`srai`/`addw`), the dispatch lemma (jump table)
  and the allocation fast path. Primitives: `gen_fn.py` summaries for the
  30 F1 primitives against `primF1Impl`.
* Budget: G1 (PLAN §GC) — `Fits` with the minor heap as the heap budget;
  the slow path is excluded by `Fits`.
* **Exit**: `ArmSim L B P` for every `P`; hence
  `ocamlrun_refinement_Statement L B` by `ocamlrun_refinement_of_arms`;
  instantiated on `whileMin` with `whileMin_bcSem` gives
  `Halts c "55\n2500\n36\n" 0` for the machine. Also: a chunked
  kernel-checked `BcSem` run of the Stdlib-linked `while.ml`.

## A2–A5: F2 data, F3 objects, F4 callbacks, F5 files

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
  globals). The collector simulation must supply `ScanCoherent`, plus the
  premises the L3′ check found (`abstractions/ROUND-1.md` §2):
  * NoForgery: no scanned word looks young unless it is a young pointer;
  * RememberedComplete: every old→young field is in `ref_table`,
    maintained by `caml_modify`;
  * a lax clause for `Forward_tag` short-circuiting;
  * interior pointers only behind `Infix_tag`.
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
