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
| `Vsa/` (663 modules) | `Vsa/` | none; `Vsa.lean` imports only the copied modules |
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

**Proof instances are about the WHILE ELF.** The copied site proofs are
about the WHILE ELF's addresses (decode lemmas aside, which are per
instruction word). PHASES.md A0 retargets them to `c/ocamlrun-riscv-htif.elf`.

## New here

`OCaml/` (the scaffold), `RunBc.lean`, `c/` apart from the files above
(`Makefile`, `src/main.c`, `src/stubs.c`, `src/gen_embed.sh`,
`src/gen_prims.sh`, `src/config/`, `tests/`), `scripts/census.py`,
`scripts/bc_census.py`, `scripts/gen_opcodes.py`, `scripts/gen_layout.py`,
`scripts/check_all.sh`, `scripts/check_holes.py`, `results/`, and the
documents.

## Third party

* **OCaml 4.14.2** (`vendor/ocaml-4.14.2/`): INRIA and contributors,
  LGPL 2.1 with the OCaml linking exception (`vendor/ocaml-4.14.2/LICENSE`).
  From `https://github.com/ocaml/ocaml/archive/refs/tags/4.14.2.tar.gz`,
  sha256 `c2d706432f93ba85bd3383fa451d74543c32a4e84a1afaf3e8ace18f7f097b43`.
  Vendored unmodified, except that `testsuite/` and `manual/` are left
  out. The bare-metal build compiles the runtime sources unmodified: the
  platform lives in `c/src/config/` (hand-written `m.h`/`s.h`/`build_config.h`
  in place of `configure`'s output; `version.h` from the 4.14.2 build),
  `c/src/main.c` (in place of `runtime/main.c`) and `c/src/htif.c`. The ELF
  links the unmodified runtime, which the linking exception covers.
  `boot/ocamlc` is the release's checked-in bootstrap compiler.
* **Sail RISC-V model** (`riscv-lean/Lean_RV64D*`, `riscv-lean/lean_emulator`):
  BSD-2-Clause (`riscv-lean/LICENCE-sail-riscv`).
* **lean-sail** (`riscv-lean/lean-sail/`): rems-project/lean-sail, patched by
  ship-your-interpreter.
* **newlib / libgcc** (linked into the ELF from the xPack
  `riscv-none-elf-gcc` 15.2.0-1 toolchain): newlib's BSD-style licences,
  GCC runtime library exception.
* **Lean dependencies** (`iris-lean`, `batteries`, `Qq`, `ELFSage`, `Cli`):
  fetched by Lake under their own licences.
