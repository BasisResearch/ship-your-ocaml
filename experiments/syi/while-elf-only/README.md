# Proofs about the WHILE ELF only (not built)

These 22 modules are ship-your-interpreter's proofs of `snprintf` /
`_svfprintf_r`, `strcmp`, `__ssprint_r` and `__ssputs_r`, copied unchanged.
They are out of the build because their facts are about code that is not
byte-identical in `c/ocamlrun-riscv-htif.elf`:

* `_svfprintf_r`, `snprintf`, `_localeconv_r`, `__locale_mb_cur_max`: the
  code differs (relaxation and a different configuration);
* `strcmp`, `__ssprint_r`, `__ssputs_r`: identical except at call sites or
  global loads (`jal` targets, the `auipc`/`ld` of `mask`) — 8 instruction
  words in all (`results/port_new_words.txt`).

`scripts/retarget_syi.py` ports the byte-identical functions' proofs; these
need regeneration for this ELF (new code lemmas, decode lemmas for the
changed words, and re-running the site generators): PHASES.md A0. Nothing
in `Vsa/`, `VsaIris/` or `OCaml/` imports them.
