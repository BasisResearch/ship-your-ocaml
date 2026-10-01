# Lane bprime

## Status

The proof/build exit criteria are met: all 23,678 backend instructions have
building generated rules, and `jumpStop_adequacy` instantiates
`bytecode_adequacy` on a generated function summary. Allocation and locality
milestones landed via `scripts/integrate.sh` as `a4d7b7a` and `65da6fc`;
both full gates passed. The generated-rule milestone uses the same full
integration gate. No lane proof/build obligations or user decisions remain.

## Proved

- `Heap.get_alloc_old`, `Heap.get_alloc_fresh`, `field_alloc_fresh`,
  `field_alloc_old` (`OCaml/Logic/Symbolic.lean:26`): allocation preserves old
  locations and exposes the new block, including infix fields.
- `closure_capture_read` (`OCaml/Logic/Symbolic.lean:59`) and the generated
  `capture_summary` (`OCaml/Programs/Generated/Demo.lean`): CLOSURE/GETFIELD2
  captures and retrieves any accumulator on an arbitrary heap and stack.
- `Run.iter_eq_of_agree` and `Run.iter_ok_of_step` (`OCaml/Run/Local.lean`):
  local agreement and partial simulation through the adopted run kernel.
- `decodeAt_local`, `code_extract_word`, `decodeAt_extract`,
  `CodeSlice.iter_eq`, `decoded_run_sound` (`OCaml/Logic/CodeSlice.lean:22`):
  instruction extraction and run locality with absolute PCs. The last
  instruction may leave a window; saved PCs and closure pointers are unchanged.
- `CertifiedBlock.decode_sound` and `CertifiedBlock.run`
  (`OCaml/Logic/Block.lean:29`): checked decoder entries lift a successful
  symbolic window run to the real program. A named `pin` premise states the
  exact extracted words required of the surrounding program.
- `call_summary`, `tail_summary` (`OCaml/Logic/Application.lean:28`): compose
  generated call prefixes, full-state application summaries and continuations.
  `apply1_enter`, `return_over`, `grab_under`, `restart_partial`
  (`OCaml/Logic/ApplicationSteps.lean:18`) reduce the real application arms.
  Summary predicates retain extra arguments, environment and caller frame.
  Back edges use the existing `loop_rule`; function termination/postconditions
  remain the client program proof's work.
- `jumpStop_summary` is generated through `runbc --lean` and instantiated via
  `jump_runFact`, `jump_wp`, `jump_hyp`, `jumpStop_adequacy`
  (`OCaml/Programs/GeneratedAdequacy.lean:12`). The last theorem invokes
  `bytecode_adequacy` with proved ownership and WP, leaving no client premise.
  This is a small branch/STOP fixture, not a proof of compiler termination.
- `pc_eq_of_reg` and `pc_alias_excluded` (`OCaml/Logic/BcModel.lean:95`):
  `bcModel.ok` now bounds the natural PC by 2^64. This makes the 64-bit PC
  ghost cell usable without aliasing; initial states satisfy the bound.

## Generated coverage and reproduction

`python3 scripts/gen_bc_rules.py` cross-checks host OCaml 4.14.4 dumpobj
instruction boundaries/opcodes against the vendored executable's CODE.
Closure entries delimit function regions; control-flow targets, transfers,
calls and 16-instruction cuts delimit windows. Signed operands come from
CODE. Every instruction appears in exactly one block. One lookahead word
supports decoder locality but is not an executable site.

| Module | Instructions | Blocks | Function regions | Measured wall | Peak RSS |
|---|---:|---:|---:|---:|---:|
| Translcore | 4,741 | 1,004 | 99 | 75.33 s | 1,505,620 KiB |
| Matching | 12,175 | 2,792 | 386 | 243.75 s | 3,204,964 KiB |
| Bytegen | 4,759 | 1,113 | 68 | 235.05 s | 1,577,300 KiB |
| Emitcode | 2,003 | 505 | 32 | 38.55 s | 988,696 KiB |
| Total | 23,678 | 5,414 | 585 | | |

Builds use default heartbeats and a 24 GiB cgroup, one lake build at a time.
Timings include shared-machine contention. `scripts/measure_bc_rules.py`
rebuilds only the selected generated modules and records source hashes,
wall/CPU time and peak RSS. Generated rules are checked at a5, and
`scripts/check_bc_audit.py` audits every generated block theorem against the
manifest. The root audit covers all handwritten headline theorems and the
end-to-end example. `scripts/gen_bc_demo.py --check` checks the fixtures.

The rules accept a code-window pin and a successful symbolic local run.
They certify the actual instruction semantics without inventing behaviour
for unsupported opcodes. Per-function semantic specifications, source-level
compiler correctness and growth of BcSem's fragment belong to subsequent
program proofs / other lanes.

## Evidence and integration

- A broad simplifier across an unresolved instruction reached the default
  200,000 heartbeat limit. Restricting reduction to the decoded instruction
  fixes it; no budget was raised.
- PC ghost encoding aliases 0 and 2^64; `pc_alias_excluded` checks the reason
  for the new `ok` bound. No BcSem transition was changed.
- Census correction: the compiler has 655,922 words and 412,087 instructions
  (VALIDATION.md:243); the lane brief calls the instruction count words.
- All four measured builds passed. Measurements and source hashes are saved
  in `results/bprime_build.json`. Final landing uses `scripts/integrate.sh`,
  including the generated-rule audit and full a1–a8/t1 gates.

## Fixed-address embedded-image migration (2026-10-01)

The foreman announced that a0-boot will move the embedded program to a
fixed-address `.embed` section and regenerate native data/code pins. Any
native data address used by this lane must come from `OCaml/Vm/Layout.lean`.
The bytecode generators and logic currently contain no native data addresses:
their PCs are CODE word indices. The hexadecimal constant in `gen_bc_demo.py`
is an OCaml Marshal format marker, not an address.

Rebased onto main `a22f2b9` and reran `scripts/gen_bc_rules.py` and
`scripts/gen_bc_demo.py`; both artefact sets are unchanged. The migration is
not in that revision. Main's new BcSem opcode semantics require the ordinary
integration build/audit even though the generated source is unchanged.
After the migration lands, rebase again, rerun both generators, and validate
through `scripts/integrate.sh`. Native Layout/decode/pin regeneration belongs
to a0-boot's migration landing.
