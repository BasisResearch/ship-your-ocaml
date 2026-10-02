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

Initially rebased onto main `a22f2b9`; integration then caught up through
`772e509`, including the expanded BcSem definitions and audit import closure.
Landed the address audit as `bce2437` through `scripts/integrate.sh`: all
a1–a8/t1 stages passed, including 784 headline theorem audits and all 5,414
generated block-rule audits. Reran `scripts/gen_bc_rules.py` and
`scripts/gen_bc_demo.py` after that landing; both artefact sets are unchanged.
The image migration is not in that revision, so its follow-up remains open.
After the migration lands, rebase again, rerun both generators, and validate
through `scripts/integrate.sh`. Native Layout/decode/pin regeneration belongs
to a0-boot's migration landing.

## Round 2: stopped at the required abstraction gate (2026-10-02)

**Discovery round required before further C4 proof expansion.** Running
`python3 scripts/check_abstraction_gate.py` after registering the new hand
proofs produced:

```
C4-bytecode-specs: 10 hand proofs, first-quarter mean 7.5 lines, last-quarter mean 18.0: FLAT
gate: cluster(s) C4-bytecode-specs reached 8 hand proofs without the per-case cost falling by a third — run /abstraction-discovery
```

The seven added census entries are `length_loop`, `length_application`,
`abs_runFact`, `abs_haltFact`, `abs_wp`, `abs_hyp`, and
`compiler_abs_adequacy`, alongside the three existing CountLoop entries.
The lane brief explicitly requires stopping for a separately run discovery
round. Proof expansion has stopped. The gate has not been bypassed; Round 2
exit is **not met**, and the proof changes below are a preserved local draft,
not landed proofs. This log is being landed separately so the foreman can
see the obstruction without accepting proof changes that fail a8.

Completed and locally checked before the gate fired:

- Rebased through `1cfce0b`, including fixed `.embed` migration `7fa1750`;
  reran existing bytecode generators, with unchanged artifacts. Native data
  addresses still come from Layout; this lane introduces none.
- `gen_bc_all.py`: exact coverage of 412,087 instructions / 655,922 CODE
  words in 202 shards (limit 2,048 instructions), with 92,543 block rules.
  This includes initialization and the final STOP. `decodeAt_extract_tight`
  fixes the unnecessary lookahead requirement for fixed-length instructions.
- `gen_bc_functions.py`: conservative CFG census of 11,292 closure entries;
  all 6,172 generated normal/over/under application-case theorems built and
  passed standard-axiom audits across 47 shards. Per-shard measurements are
  in the draft `results/bprime_functions_build.json`.
- `gen_bc_loops.py`: both matched length-accumulator loops (entries 8372 and
  20141) built. `length_loop` uses `loop_rule` and a finite `ListSpine`
  invariant; generated summaries return the initial count plus spine length,
  preserving heap/world and restoring the caller frame.
- `gen_bc_abs.py`: finds actual Stdlib.Int.abs at CODE words [12349,12360),
  copies those bytes unchanged into a runbc-generated harness, and proves a
  functional `absWord` postcondition for every signed machine integer.
  `CompilerFunctionAdequacy.compiler_abs_adequacy` builds through
  `bytecode_adequacy`; `harness_run` proves the returned value is seven on -7.
  This is a compiler-helper harness, not termination of boot/ocamlc.
- `bcModel` adds the missing extra-argument representation bound; the
  draft `extra_alias_excluded` checks why ghost-word zero alone cannot rule
  out over-application at `extra = 2^64`. The earlier adequacy fixture builds
  with the strengthened bound.
- Draft coverage: 285/11,292 normal function summaries (2.52%), 282 over
  cases, 5,608/5,608 GRAB under cases (49.66% of all entries), two ranked list
  loops. General higher-order callees remain unresolved: 34,125 unique call
  sites. The census does not miscount partial-closure returns as saturated
  function proofs or CFG back edges as dynamic tail-recursive loops.
- Hole and discipline checks passed. Full compiler shard measurement is
  incomplete: six shards have sequential build/audit/resource records in
  `results/bprime_all_build.json`. A batching prototype did not invoke its
  timing wrapper and was discarded; no fabricated timings were recorded.

Next, after the separate discovery round: adopt its C4 abstraction, finish
all 202 shard measurements using `check_bc_all.py --measure --resume`, rerun
all generator and axiom gates, and land the proof changes with
`scripts/integrate.sh`. PHASES Round 2 remains open in the draft.

Recovery snapshot: git stash `f94e122806aa291761f8f0560015f789ab85426d`
(`bprime Round 2 draft stopped by C4 abstraction gate; preserve for discovery`).
The draft will be restored in this worktree after the log-only integration;
the snapshot is retained as a recovery copy.
