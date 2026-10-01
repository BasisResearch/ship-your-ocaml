# Ship your OCaml

This project will verify **OCaml's bootstrap compiler**: the checked-in
bytes of `boot/ocamlc` (OCaml 4.14.4), run by the bytecode interpreter
`ocamlrun` compiled for bare-metal RV64 (`c/ocamlrun-riscv-htif.elf`) on the
Sail RISC-V model, in Lean 4 + iris-lean. It is a sibling of
[ship-your-interpreter](https://github.com/BasisResearch/ship-your-interpreter),
which proved a WHILE interpreter's ELF against a big-step semantics
(`endToEnd_refinement`), and of
[ship-your-lua](https://github.com/BasisResearch/ship-your-lua). It reuses
their machine layer (ATTRIBUTION.md).

**Status.** Phase 1 (validation) is done: `ocamlrun` runs on Sail —
`while.ml`, nine difftests, `boot/ocamlc -version`, and `boot/ocamlc`
compiling a program (VALIDATION.md). The Lean scaffold builds and
`scripts/check_all.sh` passes. The headline theorems are *stated* as
`Prop`s, never `sorry` or axioms; their compositions, the determinism
theory of `BcSem`, the bytecode program logic's adequacy and a kernel-checked
`BcSem` run of a real executable are *proved*. PHASES.md is the plan and
the obligation ledger; PLAN.md explains it.

**Trusted base: `tcb/`.** Everything the theorems assume rather than prove
is listed in `tcb/README.md`. The largest item is the OS interface, a Lean
port of SibylFS (POSIX file-system calls, Linux flavour) and of CakeML's
console-stream model, validated SibylFS-style on 6,490 generated scripts
run on Linux (every trace accepted). On this bare-metal build the "OS" is
`c/src/htif.c`, code inside the ELF, so the same spec is a proof obligation
(`OCaml.Os.HtifFsImplements`) rather than an assumption; on Linux it is
the assumption about the kernel (PLAN.md §6).

**One runtime image.** Program files, argv and environment live in a fixed
`.embed` region, so changing the program does not relocate runtime code or
data. The migration rechecks all generated image/library pins and proofs;
VALIDATION.md records all five successful Sail reruns.

**Reused machine proofs.** ship-your-interpreter's proofs of the library
code both binaries share (`memcpy`, `memset`, `strlen`, `strcpy`,
`__muldi3`, the division routines, …: 66 byte-identical functions) are
retargeted to this ELF's addresses by `scripts/retarget_syi.py`; the
39,600 code bytes they pin are checked against the ELF.

`WhileMin.loaded_fillZero` proves `Loaded` for the complete captured
while_min entry state, including its heap, collector invariant, platform
and primitive bindings. A native Sail rerun checks every captured memory
byte and register; reset-to-cut execution is not yet kernel-proved.

## The plan

```
OCamlSem p          ↔  BcSem (ocamlc p)    ↔  Halts c out e        a user program
     Layer C: ocamlc_backend_correct       Layer A: ocamlrun_refinement

BcSem (boot/ocamlc) ↔  OCamlSem (ocamlc's sources)                 the compiler
     boot_ocamlc_fixpoint + Layer C for the compiler's own build

Layer B′: a machine-style program logic over BcSem, and the exponentiating
          layer re-targeted at bytecode — how compiler-sized bytecode gets proved
```

**Layer A: `ocamlrun` against the ZINC bytecode semantics `BcSem`.** The
cut point is `caml_interprete(code, size)` with the executable loaded:
code, primitive table, unmarshalled global data, `Sys.argv` (`Loaded`,
`OCaml/Refinement.lean`). `BcSem` (`OCaml/Bytecode/Semantics.lean`) is a
deterministic step function transcribed arm by arm from `interp.c`, with an
abstract heap that is never collected, integer operations on the tagged
words exactly as the C, and C primitives specified one by one (channels
buffer exactly as `io.c`). It grows fragment by fragment — F1 core ZINC,
F2 data, F3 objects, F4 callbacks, F5 files, then the GC — and every
opcode outside F1 is in `Fragment.lean`'s ledger (`ledger_exact`, by
`decide`). Consequence: every bytecode program, `boot/ocamlc` included,
gets a formal meaning.

**Layer B′: a program logic over `BcSem`.** `bcModel P` presents the ZINC
machine as a `VsaIris.MachineModel` (the MachCSL pattern with `BcSem` as
the ISA), so ship-your-interpreter's iris WP and adequacy apply:
`bytecode_logic_adequacy` is proved. The generators that made the WHILE
proof scale (disassembly → segments → per-segment WP rules) are
re-targeted at `dumpobj` output.

**Layer C: the compiler at the source level.** `OCamlSem` (LLM-written, on
Lambda first — `OCaml/Source/Lambda.lean` has the syntax — then the typed
tree); the back half of `ocamlc` (Translcore/Matching → Lambda →
Bytegen → Emitcode) proved correct *as an OCaml program* with a program
logic over `OCamlSem`; then ONE translation validation, the **bootstrap
fixpoint**: under `OCamlSem`, the compiler compiles its own sources to
exactly the bytes of `boot/ocamlc`. With backend correctness for that build
this gives `boot_meaning` (proved): `BcSem` of the bytes *is* the source
compiler — without verifying its 412k bytecode instructions one by one. For
4.14.4 the host check agrees: rebuilding the compiler with `boot/ocamlc`
reproduces its CODE, PRIM, SYMB and CRCS byte for byte, and DATA up to
`configure`'s install paths. Parser and typechecker are trusted (a
parameter `parse`) or validated per program at first.

**GC strategy** (PLAN.md §3). `VmRepr` is `∃ placement, VmReprAt …` and
constrains only blocks reachable from the roots, so a moving collection is
a change of placement and sweeping is invisible. G1 first: a minor heap
large enough that no collection runs after the cut point (`Fits` budget) —
measured: eight of the nine difftests never collect after the cut at the
default minor heap (the allocation test does, 3 times). Then G2: prove the copying minor collection preserves the
representation up to a new placement, the major heap is non-moving, and
compaction stays off. `ocamlc` allocates heavily, so G2 is on the critical
path of the bootstrap theorem.

**Fragment order**: F1 (134 opcodes: stack, env, integers, branches,
`SWITCH`, globals, blocks, closures, application, traps, `STOP`, 30
primitives) → F2 data → F3 objects (`GETPUBMET` writes into the code) →
F4 callbacks → F5 files → GC. `boot/ocamlc` needs all of them: 132
opcodes, 257 primitives.

## Statements (`OCaml/Theorems.lean`)

```lean
def ocamlrun_refinement_Statement (L : Layout) (B : Budget) : Prop :=
  ∀ P c, Loaded L P c → Good P → Fits B P →
    (∀ out e, BcHalts P out e ↔ Halts c out e) ∧ (BcDiverges P ↔ Diverges c)

def ocamlc_backend_correct_Statement S ocamlc parse load : Prop :=
  ∀ src sp out fs' b, parse src = some sp →
    S.Run ocamlc compileArgv (srcFiles src) out 0 fs' → lookupFile fs' "/out/a.out" = some b →
    ∀ argv fs P, load b argv fs = some P →
      (∀ o e fs'', BcRun P o e fs'' ↔ S.Run sp argv fs o e fs'') ∧ (BcDiverges P ↔ S.Div sp argv fs)

def boot_ocamlc_fixpoint_Statement S ocamlc bs boot : Prop :=
  ∃ out fs', S.Run ocamlc bs.argv bs.sources out 0 fs' ∧ lookupFile fs' bs.output = some boot

def endToEnd_ocaml_Statement S parse load boot L B : Prop :=   -- EndToEnd
  ∀ src sp Pc out fs' b P c, parse src = some sp →
    load boot compileArgv (srcFiles src) = some Pc → BcRun Pc out 0 fs' →
    lookupFile fs' "/out/a.out" = some b → load b [] [] = some P →
    Loaded L P c → Good P → Fits B P →
      (∀ o e, (∃ fs'', S.Run sp [] [] o e fs'') ↔ Halts c o e) ∧ (S.Div sp [] [] ↔ Diverges c)
```

**Proved** (only `propext`, `Classical.choice`, `Quot.sound`;
`scripts/check_all.sh` stage a3 audits 23 theorems, stage t1 the `tcb/` lemmas):

* `endToEnd_of_layers` / `endToEnd_ocaml`: Layer A ∧ Layer C ∧ fixpoint →
  end to end; `boot_meaning`: fixpoint ∧ backend correctness → the bytes
  mean the compiler.
* `ocamlrun_refinement_of_arms`: Layer A from per-arm obligations
  (`ArmSim`: entry, one per `caml_interprete` arm, halt) via
  `simOfArms` and `ocamlrun_refinement_of_sim` (CompCert-style: forward
  simulation + determinism of both sides); `ocamlrun_refinement_fillZero`
  in the dense-memory form ship-your-interpreter states.
* `halts_or_diverges`, `BcHalts.det`, `BcHalts.not_diverges`,
  `bcHalts_of_runTo`: the determinism theory of `BcSem`.
* `bytecode_logic_adequacy`: Layer B′'s adequacy, an instance of
  `VsaIris.mach_adequacy`.
* `whileMin_bcSem : BcHalts whileMin "55\n2500\n36\n" 0` by kernel
  evaluation of a real executable (the ELF prints the same on Sail).
* `ledger_exact`, `ledger_fragment`, `f1_count`, `primF1_unsupported`.

## Validation numbers (VALIDATION.md)

| | |
|---|---|
| `while.ml` on Sail | `55\n2500\n36\n`, exit 0, 4,571,381 steps; cut point at 4,499,123 (startup: code MD5 and primitive resolution) |
| difftests (host `ocamlrun` vs Sail) | 9/9 pass (ints, closures, data, exceptions, strings/`Printf`, allocation, soft-float, objects); 4.6M–222M steps |
| `boot/ocamlc -version` on Sail | `4.14.4`, exit 0, 54.4M steps (cut at 48.8M) |
| `boot/ocamlc -dinstr -c hello.ml` (`let () = print_int (6 * 7)`) on Sail | the compiler's bytecode listing, exit 0, 82.6M steps (cut at 48.8M); one collection, forced by a channel's custom-block accounting; none with `OCAMLRUNPARAM=M=1000` (77.4M steps) |
| OS spec (`tcb/`) | 6,490 scripts, 101,621 calls on Linux: 0 traces rejected; the in-image file system: 6,410 accepted, 0 rejected (80 unconstrained) |
| reused proofs | 66 functions retargeted, 39,600 pinned bytes = the ELF's |
| `BcSem` vs binary | identical output on `while`, `f2_closures` (118,120 ZINC steps), `while_min` (kernel-checked); never `.wrong` |
| ELF census | 1,129 reachable functions, 78,529 instructions; `caml_interprete` 1,966 instructions, 147 arms, median 7; 93.9% in existing site classes; 130 functions identical to the WHILE ELF |
| bytecode census | `boot/ocamlc` 412,087 instructions, 165 units; Translcore+Matching+Bytegen+Emitcode 23,678 |
| fixpoint | rebuilt `ocamlc` = `boot/ocamlc` on CODE/PRIM/SYMB/CRCS; DATA up to install paths |

## Layout

| path | what |
|---|---|
| `OCaml/Bytecode/` | opcodes (generated), decoding, values/heap, `BcSem`, the loader |
| `OCaml/Fragment.lean` | fragments and the ledger |
| `OCaml/Vm/` | the ELF layout (generated), the representation predicate |
| `OCaml/Refinement.lean` | `Loaded`, Layer A statement, obligations, derivations |
| `OCaml/Logic/BcModel.lean` | Layer B′ |
| `OCaml/Source/`, `OCaml/EndToEnd.lean`, `OCaml/Theorems.lean` | Layer C and the composition |
| `OCaml/Programs/` | kernel-checked `BcSem` runs |
| `RunBc.lean` | `runbc`: executable `BcSem` |
| `c/` | the bare-metal build, the ELF (`ELF.sha256`), tests, Sail runner, results |
| `vendor/ocaml-4.14.4/` | OCaml 4.14.4 (LGPL 2.1 + linking exception) |
| `Vsa/`, `VsaIris/`, `riscv-lean/`, `scripts/syi/`, `experiments/syi/` | copied from ship-your-interpreter (`Vsa/` library proofs retargeted to this ELF; `experiments/syi/while-elf-only/` not built) |
| `tcb/` | the trusted base: OS spec (SibylFS/CakeML ports), checker, validation, `README.md` |
| `OCaml/Os.lean` | the bare-metal OS obligation `HtifFsImplements` |
| `scripts/` | census, generators, `retarget_syi.py`, `check_code_pins.py`, `check_all.sh` |

## Reproducing

```sh
# host OCaml 4.14.4 and the xPack toolchain in ~/toolchains (VALIDATION.md §1)
make -C c                                  # the proof ELF
sha256sum -c c/ELF.sha256 --quiet          # (from c/)
c/tests/sail_run.py c/ocamlrun-riscv-htif.elf  # needs the Lean emulator
c/tests/difftest.sh
lake build OCaml runbc && .lake/build/bin/runbc c/build/difftest/f1_while.byte
python3 scripts/census.py; python3 scripts/bc_census.py
scripts/check_all.sh
```
