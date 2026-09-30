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
| OS spec (SibylFS + CakeML port), executable checker `allowed_sound`/`allowed_complete`/`checkTrace_sound` | `tcb/TCB/Os/` | P0 | **proved**; spec **trusted** for Linux, validated on 6,490 Linux traces (0 rejected) |
| library proofs of the 66 byte-identical functions retargeted to this ELF | `Vsa/`, `scripts/retarget_syi.py` | P0 | **done** (pins checked, `memcpy_bytepath_spec`/`muldi3_spec`/`udivdi3_spec` audited) |
| `strcmp`, `__ssprint_r`, `__ssputs_r` (8 changed words), `_malloc_r`, `_free_r`, `_svfprintf_r` for this ELF | `experiments/syi/while-elf-only/` → `Vsa/` | A0 | open |
| decode for the 20,457 reachable words without a lemma (via syi's `decodeW`) | — | A0 | open |
| `HtifFsImplements` (the in-image file system meets the OS spec) | `OCaml/Os.lean` | F5 | open; `htif.c` conforms on all 6,490 validation scripts (VALIDATION §6) |
| `BcSem` world over `TCB.Os.OsState` (file/time/env primitives through `OsStep`) | `OCaml/Bytecode/Semantics.lean` | F5 | open |
| Linux instantiation: `ecall` as an external step constrained by `OsStep` | `Vsa.Machine` extension | E | open |
| `Layout.runtimeOk` concrete instance | `OCaml/Refinement.lean` | A0 | to define |
| `Loaded` at real entry states (boot witnesses, small programs) | new `OCaml/Vm/Boot/` | A0 | open |
| `ArmSim` entry + F1 arms (134 opcodes) + halt | new `OCaml/Vm/Sim/` | A1 | open |
| **`ocamlrun_refinement_Statement L B`** (Layer A, F1) | `OCaml/Theorems.lean` | A1 (by `ocamlrun_refinement_of_arms`) | open |
| F2/F3/F4/F5 arms and primitives | `OCaml/Vm/Sim/` | A2–A5 | open |
| GC: `caml_empty_minor_heap` preserves `VmReprAt` up to a new placement (G2) | new `OCaml/Vm/Gc/` | A6 | open |
| bytecode decode table / segment generators for `boot/ocamlc` | `scripts/` | B′1 | open |
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

* Done in P0: the 66 byte-identical library functions (`scripts/retarget_syi.py`).

* Instantiate `Layout.runtimeOk` with the collector's invariants at the cut
  point (minor heap bounds, `young_ptr = young_alloc_end` after the startup
  promotion, `caml_something_to_do = 0`, free-list shape as an abstract
  predicate).
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

* Decode-table and segment generators over `dumpobj` output; per-segment
  WP rules for `bcModel`; function summaries for closures.
* Route (adopted, round 1): `BcSem` specs by symbolic reduction and
  `loop_rule` (`OCaml/Logic/Symbolic.lean`; model
  `OCaml/Programs/CountLoop.lean`). Run laws come from the run kernel
  (`OCaml/Run/`). Next blocker: segments that allocate and then read the heap
  (`Heap.alloc` on a symbolic heap stays a term).
* **Exit**: the generated rules for the back-half modules (23,678
  instructions) build within the elaboration budget; `bytecode_adequacy`
  instantiated for one generated function summary end to end.

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
