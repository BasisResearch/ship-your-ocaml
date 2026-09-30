# Lane bprime

## Proved

- `Heap.get_alloc_old`, `Heap.get_alloc_fresh`, `field_alloc_fresh`,
  `field_alloc_old` (`OCaml/Logic/Symbolic.lean:26`): allocation preserves
  old reads and exposes the new block and its fields, including infix fields.
- `closure_capture_read` (`OCaml/Logic/Symbolic.lean:59`): a two-instruction
  CLOSURE/GETFIELD2 segment captures and reads an arbitrary value, with an
  arbitrary heap, stack tail, environment, extra arguments, trap and world.
  Decoder premises are explicit inputs for generated tables. Closure target
  offsets use operand 1, hence `pc + 2 + offset` in this semantics.
- All five theorem names are in `OCaml/Audit.lean`.
- Targeted build: `lake build OCaml.Logic.Symbolic` under a 24 GiB cgroup,
  default heartbeat budget, passed (545 ms module build).

- First milestone landed on main as `a4d7b7a`, full integration gate passed.
- `Run.iter_eq_of_agree` (`OCaml/Run/Local.lean:8`) transports a bounded run
  using agreement only on states visited before its bound.
- `decodeAt_local`, `code_extract_word`, `decodeAt_extract`
  (`OCaml/Logic/CodeSlice.lean:23`): decoding is local to the instruction's
  words, including variable-length operands; extraction preserves decoding.
- `CodeSlice.iter_eq` (`OCaml/Logic/CodeSlice.lean:94`) transports a run to an
  absolute-address slice decoder under explicit coverage and confinement.
  The last instruction can leave the slice. PCs and closure/return addresses
  are not rebased. All new headline facts are audited.
- Targeted locality build passed (682 ms, 24 GiB cap, default heartbeats).

## Open / next

- Generate decoder/block rules from actual bytecode; keep outputs checked at a5.
- Instantiate the proved locality rules from generated instruction tables.
- Call summaries including over/under-application and push/enter; loops use
  `loop_rule`.
- Back-half module coverage and per-module time/memory measurements.
- Instantiate `bytecode_adequacy` on a generated function summary.
- Lane exit is not yet met.

## Evidence / obstructions

A broad `simp [stepI]` across an unresolved second instruction hit the default
200,000 heartbeat limit. Reducing only after each decoder premise fixes it;
the successful proof does not raise the budget. No unresolved obstruction.

Census correction: `boot/ocamlc` contains 655,922 words and 412,087
instructions (VALIDATION.md:243); the lane brief calls the instruction count
words. The required four modules total 23,678 instructions.
