# Lane a2-sem

## Current status

Exit is open. Baseline host/BcSem differential result: 2/9 pass
(`results/bc-baseline.json`). `scripts/difftest_bc.py` compiles temporary
copies with host 4.14.4 and compares stdout and exit status without changing
the proof ELF. `scripts/syi/difftest.py` targets the copied WHILE machine
workflow, not BcSem; this runner supplies the missing bytecode comparison.

## Implemented and validated

- F2 opcode arms in `OCaml/Bytecode/Semantics.lean`: float records,
  vector length/access/update, byte/string access/update, C_CALLN.
  Transcribed from `runtime/interp.c` lines 719–816 and 962–972.
- Data primitive subset from `runtime/{array,str,compare}.c`: generic
  arrays, bytes create/blit/fill/access, and structural comparison of
  integers, strings, objects and ordinary blocks. Bounds failures allocate
  `Invalid_argument` using the actual global exception constructor.
- `OCaml/Bytecode/Data.lean` factors structural comparison; exhaustion or
  unsupported value domains remain explicit, including custom/float values.
- `lake build runbc OCaml.Fragment` passes under 24 GiB. Four of nine
  difftests pass (`results/bc-data.json`); `c/tests/bc/f2_ops.ml` also passes.
- No new theorem claims. Machine-arm proofs remain owned by a1-arms.

## Open / next

Complete the nine differential programs, update fragment coverage, then
callbacks and OS world migration. Add the actually executed compiler
opcode/primitive census and account for every entry. Relax the representation
of GETPUBMET cache words without weakening other code pins. Reduce
`HtifFsImplements` to concrete named typed function obligations with trace
validation evidence. Update PHASES rows as each part is checked.

Representation caveat: bytes allocation currently chooses zero for C's
uninitialized payload; a defined-read discipline or explicit initialization
state is needed before claiming a machine refinement of this primitive.
