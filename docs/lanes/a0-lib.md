# A0 library lane

## Current status

**Lane exit criterion met.** All six requested functions have specs at this
ELF’s addresses, pinned and audited. Final proof milestone `86cf6c9` landed on
main through `scripts/integrate.sh`; every `check_all.sh` stage passed, including
a8. The reachable-word decode coverage is generated and drift-checked by a5,
and the PHASES.md ledger is updated. No lane work remains open.

- `strcmp`: `strcmp_full_spec_cond`.
- `__ssputs_r`: `ssputs_fast_spec`, plus the general string-FILE `ssputs_nw`.
- `__ssprint_r`: `ssprint_iov2_spec`, plus the iovec-loop `ssprint_nw`.
- `_malloc_r`: `malloc_all`, with proved malloc wrapper run contracts.
- `_free_r`: `free_body`, with proved free wrapper run contracts.
- `_svfprintf_r`: `svfprintf_nw`, for literal text, `%s`, and `%d` under the
  initialization and bounded-output hypotheses detailed below.

The final audit checks 341 theorems. Code pins cover 37,048 bytes with zero
mismatches; the decoder covers 29,475 distinct disassembled words in 231 chunks.


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

## Earlier checkpoints / remaining work at those checkpoints

- `_svfprintf_r` is the remaining open function contract. `_free_r`
  (`free_body`, `FreeTop.lean:339`) and the free wrapper run contracts now
  are proved and audited; their checkpoint landed as `7c1d052`. `_malloc_r`
  is proved and audited (`malloc_all`, `MallocBlocks2.lean:718`), and its
  malloc wrapper run contracts landed as `270ae83`.
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

## Allocator composition in progress

The symbolic-run infrastructure landed as `c51817f` with the full gate
passing. The next composition templates come from syi-exp
`412ce9b2f9eae68892f58893805ae3be611a0ebc` (before on-demand step generation).
A generic import cut reduces the missing closure from 176 to 43 modules.
`scripts/retarget_allocator_specs.py` currently emits those modules plus the generic proof-piece combinator
from preserved templates; they are not all compiled yet.

Two layout assumptions needed substantive correction:

- The old allocator-global interval spanning `brk.0` and three statistics
  now contains intervening OCaml globals. The footprint splits that interval
  into the actual `brk.0` word and statistics range. `HeapShape` has compiled
  with this narrower footprint.
- `__malloc_av_` is `0x800691f8`, hence 8 modulo 16. The old `binAt_geo`
  conclusion `% 16 = 0` failed in Lean. `DlHeap.bin_base_alignment` proves
  the counterexample by kernel `decide`. Bin-node lemmas now require word
  alignment, while arena chunks retain 16-byte alignment.
  `HeapAt.node_fields_ne` separates forward/backward links using bin/arena
  geometry; the adapted `HeapTake` has compiled. No false alignment premise
  is added to function contracts.

Regeneration maps 26 expanded global-access groups across the helper
closure and one instruction scheduling move in `_sbrk`'s error epilogue.
Static `_impure_ptr` bytes are read from this ELF. Driver fuel bounds with
explicit stop PCs account for expansions; Lean heartbeat limits are unchanged.
`Sbrk`, `MallocCtx`, `HeapClear`, `HeapSplit`, and `HeapGrow` now compile.
The stack/global separation lemma now states disjointness from the two
actual helper words (`brk.0` and `errno`); its old continuous-span conclusion
was false after relocation because the new global layout has large gaps.
Read-only AUIPC loads of `_impure_ptr` use the pinned image, with an explicit
computed-address equality, rather than requiring ownership of that word.
The retargeter also relocates decimal address literals. Remaining heap
field-separation fixes reuse `HeapAt.node_fields_ne`; malloc/free function
compositions are still being checked.

`HeapCarve`, `HeapMoveAt`, `HeapFree`, and `MallocPaths` now compile.
`HeapAt.node_header_disjoint` factors the shared link/header separation
argument. The small-allocation proof reached the default 200,000-heartbeat
limit after adaptation; upstream `#ix_piece` / `#ix_chain` now splits it into
two declarations, which compile without increasing the limit. The pending
build has advanced to the higher-level machine paths.

The checked checkpoint now contains 28 generated modules, including
`MallocTop.top_split` (namespace `VsaIris.VsaHeap`), `ext_grow`, and
`extend_top`; both growth proof pieces compile within the default budget.
`checked-modules.json` selects the promoted closure; `--include-pending`
emits the remaining preserved composition templates for continued work.
The a5 drift check uses the checked manifest. The next modules are
`MallocSplit` through `MallocRunAll`, then the free paths; those full
function contracts and `_svfprintf_r` remain open.

Checkpoint audit passed for all 19 added headline facts: dependencies are
only `{propext, Classical.choice, Quot.sound}` (the concrete alignment fact
has no axioms). Entry points include `small_take` in `MallocPaths.lean`,
`top_split` in `MallocTop.lean`, and `extend_top` in `MallocExtend.lean`.
The full integration gate passed and the checkpoint landed as `46187da`.
The lane exit criterion remains unmet; function-level composition continues.

After the checkpoint, `MallocSplit`, `MallocRebin`, and `MallocRebinL`
compiled. The large-bin return proof exposed an `omega` proof-term type
mismatch involving existential witness expressions in its large context;
`link_words_disjoint` isolates the word-alignment arithmetic with three
explicit hypotheses. The remaining block scanner now carries word alignment
and a proved `links_ne` field, replacing its old 16-byte sentinel assumption.
These later modules are still pending promotion into the checked manifest.

`MallocLarge` and `MallocChain` also compile. `AlignedWordLog` adds the
checked generic theorem `read64_word_log`: aligned eight-byte writes can
be reflected into a first-order address lookup. `MallocBlocks.bw_split_ret`
is being refactored to use that theorem in checked proof pieces; combined
read simplification exceeded the default heartbeat budget. No budget was
raised. This refactor and the full malloc/free compositions remain pending.

The complete malloc composition now builds: `malloc_all` at
`VsaIris/Vsa/MallocBlocks2.lean:718` proves the `_malloc_r` entry
(`0x800375b8`); `mallocChgRun_proved` and `mallocLocalRun_proved` in
`MallocRunAll.lean` provide the wrapper run contracts. The split-return
reflection is composed from kernel-checked pieces at the default budget.
The checked manifest now selects 37 modules. All six newly added audit
entries passed with only `{propext, Classical.choice, Quot.sound}`; the
integration gate passed and landed `270ae83`. `_free_r` and `_svfprintf_r`
remain open.

Malloc checkpoint `270ae83` landed through `scripts/integrate.sh`; the full
gate passed (37,048 pinned bytes, zero mismatches). Free setup/prologue
compile; `FreeBin` requires link-field and whole-header separation under
the relocated sentinel alignment. Two shared geometry lemmas now express
those obligations and are being checked with the free composition.

`FreeBin`, `FreeLarge`, and `FreePaths` now compile. Forward/backward
coalescing uses word-aligned neighbor records with explicit link/header
separation. An old explicit AUIPC register expression failed its address
equality; the retargeter now checks its source fields and regenerates both
immediates from the new ELF. The current build is checking trim/top/entry.

The complete free composition builds: `free_body` in `FreeTop.lean:339`
starts at `_free_r` (`0x80044868`); `freeChgRun_proved` and
`freeLocalRun_proved` in `FreeRunAll.lean` establish the wrapper contracts.
`trim_fin` is composed from two checked pieces after adding the actual
mallinfo/stack disjointness fact. The checked manifest selects all 45
allocator-template modules. All six new headline audits passed with only
`{propext, Classical.choice, Quot.sound}`; integration is next. Only the
`_svfprintf_r` function composition remains open.

Free checkpoint `7c1d052` landed through the full integration gate. Work
on the remaining `_svfprintf_r` contract starts from the preserved Snp
proofs at syi-exp `412ce9b2`. Generic data-read, observed-step and driver
modules are being cut free of interpreter/WHILE dependencies. The old
conversion-table address is unnamed; its new base is derived from the
matched AUIPC reference, and table entries will be checked against the
mapped dispatch targets.

The stdio matcher now validates 13 function layouts and all 91 conversion-table
jump targets. Four GP accesses become generated two-instruction segments. All
18 preserved step chunks compile, as do `memmove_nw` (`SnpMove.lean:568`),
`strlen_nw` (`SnpStrlen.lean:281`), `udiv_nw` / `umod_nw` (`SnpArith`), and
`ssputs_nw` (`SnpPuts.lean:177`). Fresh code/table byte images use bounded lookup
trees. Expanded locale address expressions are retained until symbolic
normalization, avoiding excessive definitional reduction without raising the
heartbeat budget. Generic formatting/decimal-rendering facts also compile.
Current work: checking `SnpPrint`, then formatter entry/conversions/loop and
`svfprintf_nw`. The abstraction gate and proof-discipline checks still pass.

The complete iovec `ssprint_nw` contract (`SnpPrint`) now compiles. Its
`ssprint_iterB` composition uses two checked pieces and eliminates the
impossible error-return branch before driving the remaining instructions.
The checked stdio manifest now contains 40 template modules (plus the generated
byte-image module); formatter entry/conversion/loop templates remain pending.

Stdio foundation checkpoint `1758f28` landed on main through the full gate.
The first formatter-core build identified heartbeat limits in `svfPro_p4`,
`svfPro2_p1`, `svf_litBody`, `svf_printSign0`, and `svf_epi`; no budget was raised.
The next adaptation shortens their generated-instruction batches and separates
the sign-flag branches with a generic checked-piece branch compositor.

The formatter split resolved the previous `svfPro2`, sign-flag and epilogue
budget failures. The next check restores the generic `Arm` 32-bit load
normalizer (which had been omitted by the import cut), and reduces each
byte-clear batch to two or three steps. Shared-memory pressure delayed this
build for about thirteen minutes; the guard resumed it after memory recovered.
`LibraryImageFacts` with the restored rules compiles.

`SnpSvf` now builds in full (274 seconds under the 24 GB cap), including
`svf_entry`, literal output, sign handling, and `svf_epi`. The checked manifest
promotes it and the generic `LibraryProofBranches` compositor. Conversion,
format-loop, and final entry-to-return composition are the remaining checks.

The first conversion-module check reached eight declaration-level heartbeat
limits. A direct ownership macro experiment regressed `SnpPrint` with recursion
depth failures, so it was reverted. The conversion proofs now separate bounded
instruction batches and positive/negative branches into kernel-checked pieces;
the next build checks those compositions without increasing any budget.

The conversion module now builds (234 seconds), followed by `SnpSvfLoop`,
`SnpFormatSupport`, and `SnpFmt`. Bounded two-instruction pieces and separate
sign cases stay within the default heartbeat budget. The eight split contracts
were independently checked against their original types; none exports an extra
body obligation. The local stack-ownership rule is confined to the conversion
module. The missing `pieceBytes_zero` import-cut helper was restored from the
preserved upstream source.

`VsaIris.Sym.svfprintf_nw` (`VsaIris/Vsa/SnpFmt.lean:314`) proves execution
from `_svfprintf_r` entry `0x8004789c` through its caller return. Its scope is
literal text plus `%s` and signed 32-bit `%d`, an initialized string FILE
(flags `0x208`), ASCII locale, at most five stack argument slots, disjoint
bounded input/output, and rendered length plus 21 below `2^31`. It establishes
the first `min(rendered length, n-1)` bytes, the full rendered length in `a0`,
restored stack/callee-saves, and a memory frame. It does not add the terminating
NUL; that belongs to the snprintf wrapper. `SvfRetK` is the ordinary caller
continuation. All 46 stdio templates plus the generated image are now selected
by the default generator and a5 drift check. The latest pin check reports
37,048 bytes and zero mismatches; all 91 table targets validate.

The root library build and `OCaml.Audit` pass (1,041 jobs). New entry,
conversion, digit-loop, and final `svfprintf_nw` audits depend only on
`{propext, Classical.choice, Quot.sound}`. Proof discipline, abstraction gate,
whitespace, and 47-module generator drift checks pass. Final integration is next.

Final proof milestone `86cf6c9` landed on main. All integration stages passed:
builds, differential validation, 341 headline axiom audits, discipline,
generator drift, ELF hash/ecall checks, code pins, TCB validation, and the
abstraction gate. This lane is complete.
