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

## Open / next

- Generate decoder/block rules from actual bytecode; keep outputs checked at a5.
- Prove code locality using the run kernel; avoid reducing whole compiler code.
- Call summaries including over/under-application and push/enter; loops use
  `loop_rule`.
- Back-half module coverage and per-module time/memory measurements.
- Instantiate `bytecode_adequacy` on a generated function summary.
- Lane exit is not yet met.

## Evidence / obstructions

A broad `simp [stepI]` across an unresolved second instruction hit the default
200,000 heartbeat limit. Reducing only after each decoder premise fixes it;
the successful proof does not raise the budget. No unresolved obstruction.
