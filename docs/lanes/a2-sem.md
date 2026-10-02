# Lane a2-sem

## Current status

Round 2 active (2026-10-02): rebased onto the fixed `.embed` image migration.
Working in brief order: OFFSET widths, initialized bytes, eleven compiler
primitive boundaries, callbacks/uncaught exceptions, concrete HTIF relation.
The Round 2 compiler differential exit is not yet met.

OFFSETINT/OFFSETREF now shift operands in 32 bits before sign extension,
matching the pinned runtime. `scripts/difftest_offsets.py` passes 16
host/runbc cases including negative operands and 32-bit shift overflow;
results are in `results/bc-offsets.json`. The original width probe passes
with `--expect-model 2`. Symbolic and CountLoop builds pass. The executed
ledger was regenerated after migration (no drift).

## Round 1 evidence

Lane exit criterion met. Implementation landed on main as `f442c8c` through
`scripts/integrate.sh` on 2026-10-01. All integration stages passed, including
784 theorem axiom reports, generator drift, 39,056 pinned bytes (zero
mismatches), OS validation and the abstraction gate.

Exit evidence:

- 121 executed opcode kinds and 86 primitive names are ledgered, with finite
  kernel-checked coverage theorems.
- All nine standard host/runbc difftests pass in the combined run
  (`results/bc-f2-f5.json`); allocation takes 8,274,724 steps.
- HTIF is reduced to named typed function premises with reproduced evidence.
- PHASES rows distinguish executable status from remaining proof obligations.

The pinned ELF migration had not landed at the final main fetch. No new
machine data addresses are hard-coded. If the lane is resumed after a0
lands the migration, rebase and regenerate the lane census artifact with
`python3 scripts/gen_executed_ledger.py`; machine pins remain Layout-derived.

## Implemented and validated

- F2's ten opcode arms; ordinary and float data, array/bytes/string
  primitives, integer formatting/parsing, rational decimal float formatting,
  fdlibm atan, boxed integer operations, and integer hash. Argument-domain
  gaps remain explicit (`compareVal` excludes custom/float values; hashing
  currently handles integers).
- F3 method lookups and object primitives. `VmReprAt.code` now identifies
  GETPUBMET cache operands by linear decoding and permits cache mutation;
  ordinary code words remain pinned. `CodeRepr` is shared with the newly
  landed primitive `VmPayload` so its frame proofs use the same contract.
  Cache hit/miss simulation and method-table well-formedness remain
  machine-arm obligations.
- World state uses `TCB.Os.OsState`. File open/read/write/seek/close,
  rename/remove/existence, environment and time select transitions through
  `TCB.Os.allowed`. Channel representation includes input buffers/cursors
  and offsets. `osCall_sound` derives `OsStep` from `allowed_sound`.
- The final combined 9/9 run passes after formatter/channel corrections.
- Focused data, format/float and buffered-file tests pass
  (`results/bc-focused.json`). Host and model execute in a temporary directory.
- The heap uses an array for executable indexing/allocation with a logical
  list view. `Heap.get?_eq_getArray` certifies its compilation rewrite;
  `storage_list_eq` and `storage_size_eq` preserve symbolic interfaces.
  Existing Symbolic and CountLoop proofs build. The word-budget definition
  retains its logical list fold for the newly landed A6 live-word bound.
  CountLoop and Forward counterexample heap literals use array notation;
  their statements and proofs are otherwise unchanged.
- Successful host boot/ocamlc hello compile measured 121 opcode kinds and
  86 primitives (`results/ocamlc-executed.json`). The generated finite census
  and `executed_{opcodes,primitives}_ledgered` account for every name, with
  explicit open primitive reasons. This is not a BcSem compiler run proof.
- Native HTIF validation reproduced 6,490 traces / 101,621 calls: 6,410
  accepted, 80 special, zero rejected/unsupported. Reproducer:
  `scripts/validate_htif_fs.py`; hashes and scope: `results/htif-fs.json`.
  `HtifFunctionObligations` names remaining per-function termination and
  partial-correctness premises; `htifFsImplements_of_functions` composes them.

## Open / next

The lane exit is complete; the following are downstream Layer A obligations.
The integer formatter uses character-list parsing; the existing `whileMin_runTo` and `whileMin_bcSem`
kernel proofs pass again (125 seconds under the 24 GiB build cap).
F4 currently supports caught exceptions and disabled raw-backtrace state;
re-entrant callbacks and uncaught-exception handling remain open. The eleven
compiler primitive boundaries in `primitiveOpen` are ledgered, not implemented.
The concrete HTIF entry classification, memory relation and generated machine
function proofs are open; trace validation does not discharge them.

Representation caveat: bytes allocation chooses zero for C's uninitialized
payload. A defined-read discipline or initialization state is needed for
machine refinement. Float execution and formatting are differential-tested
subsets, not a universal soft-float/newlib correctness theorem. WorldRepr
still needs the concrete HTIF memory relation beyond console/channel layout.

## New theorem index

- `Heap.storage_list_eq`, `Heap.storage_size_eq`, `Heap.get?_eq_getArray`:
  `OCaml/Bytecode/Value.lean:118`, `:121`, `:131`.
- `osCall_sound`: `OCaml/Bytecode/Os.lean:24`.
- `executed_opcodes_ledgered`, `executed_primitives_ledgered`:
  `OCaml/Fragment.lean:269`, `:272`.
- `htifFsImplements_of_functions`: `OCaml/Os.lean:86`.

All are included in `OCaml/Audit.lean`. The HTIF theorem is conditional;
its named premises are not supplied by the native-C trace evidence.
