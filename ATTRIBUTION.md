# Attribution

This repository reuses the language-agnostic machinery of
[ship-your-interpreter](https://github.com/BasisResearch/ship-your-interpreter)
(Basis Research), copied at commit `46b1eb8e`. Both projects are Basis
Research's. ship-your-interpreter carries no licence file; this repository
keeps that consistent and adds none of its own for its own code.
Third-party components keep their own licences, listed below.

The copy is the same file set as
[ship-your-lua](https://github.com/BasisResearch/ship-your-lua)'s (the two
lanes share the toolchain and the machine layer), so a fix to the machine
layer applies to both.

## Copied from ship-your-interpreter

| here | there | changes |
|---|---|---|
| `riscv-lean/` (without `.lake/`) | `riscv-lean/` | none (plus `README.md`, `LICENCE-sail-riscv` from ship-your-lua) |
| `Vsa/` (641 modules) | `Vsa/` | **retargeted to this ELF** by `scripts/retarget_syi.py` (below); `Vsa.lean` imports only the built modules |
| `experiments/syi/while-elf-only/` (22 modules) | `Vsa/Sim/` | none; out of the build: proofs of `snprintf`/`_svfprintf_r`, `strcmp`, `__ssprint_r`, `__ssputs_r`, whose code differs in this ELF (their README) |
| `VsaIris/` (19 modules) | `VsaIris/` | none; `VsaIris.lean` likewise |
| `scripts/syi/` | `scripts/` | none: segment and site generators (`disasm_to_segment.py`, `disasm_to_sites.py`, `gen_segment.py`, `gen_sites.py`, `genseg/`, `genseg.py`, `segment_certificates.py`, `segments/`), `gen_fn.py`, `gen_decode_index.py`, the boot-witness generator `gen_boot_witness.py`, the difftest library, `check_final_axioms.sh` |
| `experiments/syi/` | `experiments/` | none (`gen_decode_table.py`, `gen_code_lemmas.py`, `disasm_census.py`, `disasm_reachable.py`) |
| `scripts/check_discipline.py`, `scripts/discipline_rules.tsv`, `scripts/discipline_grandfather.txt`, `scripts/abs_inventory.sh` | `scripts/` | `check_discipline.py` scans `Vsa/`, `VsaIris/` and `OCaml/` (was `Vsa/` only); rules O1–O4 appended for `OCaml/` |
| `c/src/crt0.S`, `c/src/link.ld` | `c/src/` | none (via ship-your-lua, identical) |
| `c/src/htif.c` | `c/src/htif.c` | the HTIF console/exit and `_sbrk` are unchanged; the `_open`/`_read`/`_lseek`/`_fstat` stubs are replaced by an in-memory file system (embedded files + created files, directories as path prefixes) |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | same | new package name, new `OCaml` library and `runbc` executable |
| `CLAUDE.md` (the discipline) | `CLAUDE.md` | via ship-your-lua's adaptation; WHILE rows dropped, OCaml rows added |

The copied Lean modules are the import closure of the machine relation
(`Vsa.Machine`, `Vsa.Elf`, `Vsa.Triple`), densification (`Vsa.Densify.*`),
the instruction-level simulation layer and decode table (`Vsa.Sim.*`), the
libgcc/newlib site proofs, and the Iris machine logic (`VsaIris.*`). It
contains none of ship-your-interpreter's WHILE semantics or representation
(`Vsa.While.*`, `Vsa.MemRepr*`, `Vsa.Refinement`); `OCaml/Refinement.lean`
restates the refinement pattern of `Vsa/Refinement.lean` for `BcSem`.

**Retargeting.** The copied proofs of library code were stated at the
WHILE ELF's addresses. `scripts/retarget_syi.py` rewrites, in 30 files,
every address inside the 66 functions that are byte-identical in the two
ELFs (`memcpy`, `memset`, `memmove`, `strlen`, `strcpy`, `__muldi3`, the
64-bit division routines, `setjmp`/`longjmp`, …) to the same offset in this
ELF, maps function starts and data symbols by name, and moves the HTIF
mailbox constant `Vsa.Sim.tohostAddr` (`0x8001ad00` → `0x80067600`). No
proof text changed otherwise; the layer rebuilds, and
`scripts/check_code_pins.py` checks all 2,560 bytes the ported code
predicates pin against the ELF. The WHILE interpreter's own `value_*`
pins (`Vsa/Sim/Code/Value_*.lean`) remain facts about the WHILE ELF, which
other copied proofs import; nothing here uses them.

## New here

`OCaml/` (the scaffold), `RunBc.lean`, `c/` apart from the files above
(`Makefile`, `src/main.c`, `src/stubs.c`, `src/gen_embed.sh`,
`src/gen_prims.sh`, `src/config/`, `tests/`), `scripts/census.py`,
`scripts/bc_census.py`, `scripts/gen_opcodes.py`, `scripts/gen_layout.py`,
`scripts/check_all.sh`, `scripts/check_holes.py`, `results/`, and the
documents.

## Third party

* **OCaml 4.14.4** (`vendor/ocaml-4.14.4/`): INRIA and contributors,
  LGPL 2.1 with the OCaml linking exception (`vendor/ocaml-4.14.4/LICENSE`).
  From `https://github.com/ocaml/ocaml/archive/refs/tags/4.14.4.tar.gz`,
  sha256 `71415c000ebfce604defafaa584ab5ed10ad81ff180897db4e6fea8dac6e4b0d`.
  Vendored unmodified, except that `testsuite/` and `manual/` are left
  out. The bare-metal build compiles the runtime sources unmodified: the
  platform lives in `c/src/config/` (hand-written `m.h`/`s.h`/`build_config.h`
  in place of `configure`'s output; `version.h` from the 4.14.4 build),
  `c/src/main.c` (in place of `runtime/main.c`) and `c/src/htif.c`. The ELF
  links the unmodified runtime, which the linking exception covers.
  `boot/ocamlc` is the release's checked-in bootstrap compiler.
* **SibylFS** (`tcb/upstream/sibylfs/`: `t_fs_spec.lem_cppo`,
  `t_dir_heap.lem_cppo`): Tom Ridge, David Sheets, Thomas Tuerk, Andrea
  Giugliano; `sibylfs/sibylfs_src` at
  `30675bc3b91e73f7133d0c30f18857bb1f4df8fa`, ISC licence
  (`tcb/LICENSE-sibylfs`). Ported to Lean in `tcb/TCB/Os/Fs.lean` and
  `tcb/TCB/Os/Syscall.lean` (Linux flavour, files and directories; the
  deviations are listed there and in `tcb/README.md`).
* **CakeML basis file-system model** (`tcb/upstream/cakeml/fsFFIScript.sml`):
  CakeML contributors; `CakeML/cakeml` at
  `530c7deec135ad421cce7ca768eed2f5801261b2`, BSD-3-Clause
  (`tcb/LICENSE-cakeml`). Its stream model and nondeterministic
  read/write lengths are ported in `tcb/TCB/Os/Streams.lean`.
* **Sail RISC-V model** (`riscv-lean/Lean_RV64D*`, `riscv-lean/lean_emulator`):
  BSD-2-Clause (`riscv-lean/LICENCE-sail-riscv`).
* **lean-sail** (`riscv-lean/lean-sail/`): rems-project/lean-sail, patched by
  ship-your-interpreter.
* **newlib / libgcc** (linked into the ELF from the xPack
  `riscv-none-elf-gcc` 15.2.0-1 toolchain): newlib's BSD-style licences,
  GCC runtime library exception.
* **Lean dependencies** (`iris-lean`, `batteries`, `Qq`, `ELFSage`, `Cli`):
  fetched by Lake under their own licences.

## Generic machine decoder (A0 library lane)

`Vsa/Meta/SimpNF.lean` and `Vsa/Sim/DecodeNF.lean` are copied unchanged
from ship-your-interpreter's `exponentiate` worktree (`syi-exp`), commit
`69939cfcad4e6261c546419f4f71808fcc5bb70e`. The source trees were read only.
`scripts/gen_elf_decode.py` instantiates this generic decoder for all text
words in this repository's ELF, in `Vsa/Sim/ElfDecode/`. Its Python decoder
proposes statements only; each proof uses `decodeW` and kernel reduction.

The three same-layout site batteries in `Vsa/Sim/{Strcmp,Ssputs,Ssprint}Sites.lean`
are generated retargets of the preserved copies in
`experiments/syi/while-elf-only/`, from the original attribution above.
`library_layout.json` in that directory records the WHILE ELF's symbols and
three function bodies, with its SHA-256, so drift checks do not need that
external ELF. `gen_library_pins.py` reuses the preserved code-lemma generator
for the six complete code regions in this ELF.

The whole-function `StrcmpSpec{,W,W2,W3,W4,Cond}.lean` proof sources
are preserved from ship-your-interpreter commit `46b1eb8e` (the original
copy baseline) under `experiments/syi/while-elf-only/Vsa/Sim/`.
`retarget_library_sites.py` also retargets these, deriving the relocated
mask base and load address from the ELF instruction pair.
`Vsa/MemRepr.lean` keeps only the generic memory/C-string definitions
from syi-exp `69939cfc`; `StrlenSpec.lean` keeps its arithmetic helpers
and the three C-string lemmas from `46b1eb8e`. `ObsAvoid.lean` is copied
from `69939cfc`, replacing two redundant WHILE-specific observation helpers
with the identical generic helpers already present in this repository.
These import cuts introduce no WHILE runtime or WHILE code predicates.

## A1 segment boundary import cut

`Vsa/Sim/SegState.lean` ports only the `SegSt` record from
ship-your-interpreter commit `95ee5f98^`, same path. It keeps the existing
`RegPins` import and omits SnprintfSpec18, examples and unused transport
lemmas. The port uses default elaboration limits.
