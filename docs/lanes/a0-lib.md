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
  gate pending.

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

## Open / next

- All six function specifications remain open; decode facts alone do not
  discharge them. Compose the three same-layout site batteries into function specs and regenerate
  `_malloc_r`, `_free_r`, `_svfprintf_r`; pin their regions and audit specs.
- Upstream current trees have removed scripts; `gen_alloc_steps.py` and
  `rv_steps.py` are recoverable read-only from syi commit `af62bc55^`.
- The mandatory allocator `VsaIris.Vsa.SymRun` import closure currently has
  89 missing modules, including WHILE-only dependencies through MemRepr,
  MallocFastSegs, ObsAvoid, and BridgeSeg. Machine import cuts are
  prerequisites to bringing this route into the build.

## Exit

Decode coverage complete; six function specs outstanding.
