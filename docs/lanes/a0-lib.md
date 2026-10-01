# A0 library lane

## Proved

- `Vsa.Sim.decodeW` (`Vsa/Sim/DecodeNF.lean:33`): generic Sail decode
  under the machine-mode control-register assumptions. Copied with
  `#simp_nf` from syi-exp; provenance is in ATTRIBUTION.md.
- `Vsa.Sim.ElfDecode.decode_<word>` (`Vsa/Sim/ElfDecode/Part*.lean:15`):
  all 29,475 distinct words across every disassembled ELF function. This
  conservatively covers census reachability, including indirect calls.
  231 generated chunks, 128 words each (last chunk smaller), no heartbeat
  increase. Every chunk built under a 24 GB cgroup cap; typical chunk 2–4 s.
- `scripts/gen_elf_decode.py --check` checks complete generated contents
  against a fresh ELF disassembly, including missing/stale chunks; wired
  into check_all a5. The Python decoder only proposes ASTs: Lean checks
  each one against Sail using `decodeW` and `rfl`.
- OCaml/Audit.lean audits the generic equality, decodeW, and representative
  generated applications; all audited axioms are standard. Full integration
  gate passed; landed as `7e0668e`.

- Six complete code regions regenerated with the existing code-lemma
  generator (`scripts/gen_library_pins.py`); 36,264 total pinned library
  bytes checked with zero mismatches. All six modules built, including
  `_svfprintf_r` (62 seconds, within the default elaboration budget).
- `StrcmpSites`, `SsprintSites`, `SsputsSites`: existing per-instruction
  specifications retargeted mechanically and built. The two changed strcmp
  instructions and changed call immediates use this ELF's decoded words.
  Each site theorem is in the axiom audit. These are site specifications,
  not yet whole-function functional specifications.
- `scripts/retarget_library_sites.py --check` reproduces these from the
  preserved WHILE sources and a committed old-layout snapshot, without
  requiring an upstream checkout; wired into a5, alongside library pins.

- `strcmp_full_spec_cond` (`Vsa/Sim/StrcmpSpecCond.lean:104`) now proves
  the whole strcmp contract, including aligned word and unaligned byte
  paths, return sign, memory/output preservation, and the register frame.
  Its ASCII/NUL-terminated C-string, region/slack, code/mask pin and return
  alignment hypotheses are preserved from upstream. Six proof modules
  built in 3–23 seconds each. Both mask addresses are derived from this
  ELF's AUIPC/LD pair. Axiom audit passed; landed as `38d36d5`.

- `memmove_fwd_spec` (`Vsa/Sim/SnprintfSpec18.lean:1455`) and
  `ssputs_fast_spec` (`Vsa/Sim/SnprintfSpec19.lean:1083`) prove short,
  non-overlapping copies with sufficient sink capacity and framed return.
- `ssprint_iov2_spec` (`Vsa/Sim/SnprintfSpec20Part4.lean:418`) composes
  two such copies. It proves the copied bytes, advanced cursor, decremented
  capacity, cleared count/residual, return value zero, restored callee-saves
  and stack, and memory preservation outside the written windows.
- All three new headlines passed the axiom audit (only propext,
  Classical.choice, Quot.sound). The five generated ssprint modules built
  in 4, 6, 248, 104, and 6 seconds under a 24 GB cap. No heartbeat limit
  was increased. The first monolithic attempt was stopped by this lane
  after 189 seconds at over 12 GB RSS; splitting bounded elaborator memory.
- `SsprintCodeFrame` extracts four upstream code-preservation helpers.
  The new memmove region and stdio outputs are drift-checked by a5.
  `check_code_pins.py`: 36,856 pin occurrences, zero mismatches.

## Open / next

- `_malloc_r`, `_free_r`, `_svfprintf_r` function contracts remain open.
  Instruction census (old -> this ELF): 560 -> 569, 193 -> 195,
  3212 -> 3213. The added instructions expand GP-relative global accesses
  into AUIPC/load/store sequences; svfprintf expands `__global_locale`.
- Upstream generators are recoverable read-only from syi commit
  `0c4ebe85b4b99e22d30fb9920efb806578aad899`. Neither upstream repo was edited.
- The mandatory allocator symbolic-run route now builds with a generic
  import cut. `Vsa.Sim.segEval_sound` (`Vsa/Sim/SegEvalSound.lean:8`),
  `VsaIris.Inst.seg_runFact` (`VsaIris/Vsa/Instance.lean:302`), and
  `VsaIris.Sym.swp_step` / `swp_jal` (`SymRun.lean:403` / `:368`) have
  passed the standard-axiom audit. Run conversions use OCaml's existing
  kernel presentations; `iter_counter` is a generic kernel corollary.
- `scripts/syi/gen_alloc_steps.py` has regenerated 1,459 instruction-step
  lemmas across 46 modules, from 1,461 instructions in 16 allocator/helper
  functions. Every chunk built (typically 2–3 seconds), in batches of four
  within a 24 GB cap. All `_malloc_r` and `_free_r` words have step lemmas.
  The two explicitly unsupported words are in other functions: `_realloc_r`
  (`sltu`, `0x80037f0c`) and `memcpy` (`sltiu`, `0x80042858`).
- `AllocCode` pins 5,852 code/global bytes with balanced 16-byte chunks.
  The generator derives GP and `_impure_ptr` from this ELF, uses its decode
  table, and is drift-checked by a5. `gen_library_layout.py` also drift-checks
  the entry/GP constants. Representative malloc/free entry steps are audited.
- The next work is function-level composition over SWP. Normalizing global
  accesses aligns all 557 malloc and 190 free instruction groups, including
  their 9 and 2 expansions. That mapping is preparation, not a function spec.

## Exit

Decode coverage and strcmp landed (`7e0668e`, `38d36d5`). The two stdio
contracts and memmove dependency landed as `2d4953b`; the full integration
gate passed, including 285 axiom audits. The three changed-layout
function specs remain outstanding, so the lane exit criterion is not met.
