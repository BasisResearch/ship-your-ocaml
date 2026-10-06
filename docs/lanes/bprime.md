# Lane bprime

## F1 round (2026-10-05): entry, halt, final assembly

**Done**
- `OCaml/RefinementF1.lean`: the F1 domain `GoodF1` (`Good`, plus every
  reachable state decodes to an `InF1` instruction: an F1 opcode, and a
  `primsF1` name for C_CALLs), `GoodF1.of_static` (a static code check plus
  "reachable PCs decode"), and `OcamlrunRefinementF1` (same conclusion as
  `OcamlrunRefinement`, `GoodF1` for `Good`; implied by it, `OcamlrunRefinement.f1`).
- Assembly: `F1Arms P c0 R` is the arm table. It has `entry` and one
  `OpArm P R op` row per F1 opcode. Each row is stated over a loop invariant
  `R` the families choose (it may depend on `c0`, e.g. the native frame
  saved at entry). A row concludes `ArmOutcome R c (stepI P s i)`: `.next`
  means `Plus` into `R`, `.halt` means `Halts`. `ArmOutcome.of_next` and
  `ArmOutcome.of_cases` adapt existing `*_step_arm` bridges. `F1Arms.simR`
  and `ocamlrun_refinementF1_of_arms` give the headline, exposed as
  `Theorems.ocamlrun_refinement_F1_of_arms`. `ArmSim.f1Arms` shows that the
  old contract is the `Running` instance.
- `OCaml/Refinement.lean`: simulation by any relation, `SimR` /
  `run_simR` / `SimR.refines` / `refines_of_forward`. `run_sim`,
  `simOfArms` and `ocamlrun_refinement_of_sim` are now its instances, with
  the same statements.
- Why per-opcode rows carry both outcomes: one lemma "only STOP/C_CALL
  halt" over all of `stepI` hit the default 200k heartbeat limit, both via
  `split` on `stepI.eq_def` and via `cases op; simp only [stepI]`. With the
  opcode and argument shape concrete, a single opcode reduces in about 1 s.
  So each row discharges its own no-halt fact.

**Round 2 draft**: the previous session's unlanded WIP commit `7c68e6e`
(the 202-shard rules, function/loop/abs summaries; 2.5M generated lines)
fails stage a8. Its 7 new C4 hand proofs make C4 FLAT (see "Round 2"
below), and the F1 brief pauses B′ scale-up. It is NOT landed. It is kept
on the local branch `bprime-round2-draft`; `lane/bprime` was reset to
`origin/main`.

- Landed `be2742b`: the assembly above (full gate).
- `OCaml/Programs/F1Check.lean`: `runToF1` (runTo that also checks `InF1`
  decoding at every visited state) and `GoodF1.of_runToF1`. A halting
  checked run visits every reachable state, so `whileMin_goodF1` is one
  `decide +kernel` (27 s). `whileMin_halts_of_arms`: from `Loaded L whileMin c`
  and the F1 arm tables, `Halts c "55\n2500\n36\n" 0`. Its domain premises
  are discharged by `whileMin_goodF1`, `whileMin_fits` and `whileMin_gcSafe`
  (a6-gc).
- `OCaml/Vm/Sim/Invocation.lean`: `Invocation D c` is the native frame fixed
  at entry: x2 = nativeSp, the `Caml_state` pointer, and the bytes of
  `invocationRanges` = [sp, sp+32) ∪ [sp+200, sp+640). It excludes
  [sp+32, sp+192), where arm bodies spill. It is frame-shaped: arms preserve
  it from their write log alone, via `InvocationOutside` and
  `Invocation.frame`/`frame_log`/`frame_read`. Agreed with a1-arms: the F1
  invariant (since replaced by `Running.native`, see below).

- Landed `81ccb44`: F1Check and Invocation.
- The entry machine segments are generated (`gen_arm_pilot.py`) and build
  under the default limits:
  * `INTERP_ENTRY_SAVE`: 0x80001df8 → 0x80001e38, bnez taken; 7 s;
  * `INTERP_ENTRY_PREP`: → jal setjmp, loads named (opaque loads);
  * `SETJMP`: 0x80042c4c → ret; 10 s;
  * `INTERP_ENTRY_RESUME`: 0x80001e80 → 0x80001f40, beqz taken;
  * then the existing `LOOP_SETUP`.
  As one 33-step segment, the save and prep parts together hit the 200k
  heartbeat whnf limit; split in two they fit.
- `entry_save` (`OCaml/Vm/Sim/EntrySave.lean`): the prologue's exact
  13-store log, the new sp, preserved registers and the image, from the
  caller's frame. `EntryFrame`/`slot_nat`/`slot_tac` (`EntryFrame.lean`)
  normalize frame addresses once; every store premise closes by `omega`.
- `InterpCaller` (`OCaml/Vm/Caller.lean`), to become `LoadedAt.caller`: callee-saved registers with
  ra = 0x80004ff8, sp above `heapEnd`, caml_main's frame with its ra slot
  = 0x80001df0, the `Caml_state` record in the arena, and `PayloadOutside`
  of entry's write footprint. Without it, STOP's return is unconstrained
  and the statement is false. The captured whileMin cut carries it as an
  to be discharged for the closed captured whileMin witness
  (`WhileMin.loaded`) in the same commit that adds the field, so that witness
  stays closed. `InterpCaller.of_mem` transports it through `fillZero`.
- F1Loop is dropped. a1-arms moved the invocation into `Running.native`
  (`∃ D, Invocation D c ∧ NativeValid D`, with `NativeValid` as specified by
  bprime), so the table invariant is `LoopAt`.

- **`ArmSim.entry` proved** (`entry_loopAt`, `OCaml/Vm/Sim/EntryLoop.lean`).
  Starting from `LoadedAt L P c pl cp high`, the machine reaches
  `LoopAt L P P.init c'` at least one step later (all five `Running`
  fields). The run chains the generated segments:
  * `entry_save`: 13 callee-saved stores;
  * `entry_prep`: prog, `callback_depth + 1` and the four `Caml_state`
    saves, each load read back through the earlier stores;
  * `entry_setjmp`: 14 jump-buffer stores;
  * `entry_resume`: `external_raise = &raise_buf` and the initial VM registers;
  * `LOOP_SETUP`.

  The total memory effect is one `entryLog`, covered by `entryFootprint`
  (`entryLog_cover`). From that cover follow: the payload frame
  (`PayloadOutside.cover`), the primitive table, the runtime invariant via
  `WindowStable` on `entryWindows`, `StackGeometry.transport`, and the
  entry snapshot `NativePlaced`, whose `NativeValid` return slots are read
  back from the save log and caml_main's frame.

  Named premises: `InterpCaller` (now also the cut's dispatch clock and the
  primitive table's separation), `StackGeometry P P.init c pl cp high` at
  the cut, and `WindowStable L.runtimeOk (entryWindows …)`. All three become
  `LoadedAt` fields with their proof for the captured whileMin cut.

- **STOP halt** (`OCaml/Vm/Sim/Stop{Halt,Ready}.lean`):
  * `stop_do_exit_summary` discharges `StopDoExitSummary` with a1-prims'
    `do_exit_halts` (status 0; console unchanged; the quiet-exit globals read
    back through STOP's stores);
  * `stop_ready` gives `StopInvocation`/`StopCallerReady` from
    `Running.native` and the `Caml_state` placement;
  * `stop_exit_continuation` composes them for a1-arms'
    `stop_halt_step_arm`.

  Named premises: `StopExitReady` (ExitGlobals, caml_do_exit's 208-byte
  window, GPR presence and HTIF idle at caml_do_exit) and an ordinary accu
  word. The latter needs EvenPlace at mod 4 (requested from a1-arms) and
  `GoodF1.stopAccu` (new: STOP never returns a `.raw` word, which caml_main
  would read as an exception; `whileMin` still checks in one kernel run).

**InF1 minor-heap bound; whileMin's C_CALL returns (2026-10-06)**
- Foreman decision: MAKEBLOCK with `wosize > Max_young_wosize` (and CLOSURE /
  CLOSUREREC whose block exceeds it) take interp.c's `caml_alloc_shr` path and
  are outside F1. `InF1.minor : i.minorAlloc = true` (`RefinementF1.lean`,
  interp.c's own tests); ledger `Fragment.majorAllocLedger`. Rows get the
  bound from `InF1` (OpArm's premise), so BlockSizes/ClosureSizes retire.
- `CcallReturns.of_names` / `.of_primsF1` (`CcallNames.lean`): `CcallReturns`
  from per-primitive summaries `PrimReturnsAt` (a1-prims' adapters). The
  general instance needs no per-program premise.
- whileMin: `St.callNamesOk` joins the one shape run; `whileMin_ccallReturns`
  (`WhileMinCalls.lean`) uses its 7 primitives. `WhileMinOpen` is now 4
  fields: `setglobal_barrier`, and `c_call{1,2,4}_prims` (PrimReturnsAt for
  each of `whileMinCalls`).

**Deferred (2026-10-06)**: `Invocation.raiseBuf`
(`Caml_state->external_raise = D.nativeSp + raiseBufOffset`). Only the general
C-raise path needs it (a2-sem's zero-divisor row for programs that do divide
by zero), and it costs a frame hypothesis at ~90 native-frame sites (a1-arms).
whileMin does not need it: its divisors are never zero
(`whileMin_divisorsNonzero`). Entry's readback recipe, should it be added:
`word_writeLog_at` on `entryLog` at index 33 (the resume store).

**whileMin's open premises, generated (2026-10-06)**
- `WhileMinTable.lean` (generated with F1Table by `scripts/gen_f1_table.py`):
  `whileMin_halts_open (o : WhileMinOpen) : Halts WhileMin.cut "55\n2500\n36\n" 0`.
  Fields of unreached opcodes are discharged from `whileMinOps`; fields
  proved by the shape run are filled. As rows land and the generator reruns,
  `WhileMinOpen` shrinks. Currently it has 10 fields:
  * `row_CLOSURE`, `row_MAKEBLOCK` (a1-arms);
  * `setglobal_barrier` (caml_modify, a6-gc);
  * `c_call{1,2,4}_{returns,effects}` (a1-arms/a1-prims);
  * `scratch` (GPR presence in LoopRegisters, a1-arms).

**whileMin's remaining premises (2026-10-06)**
- `f1_table_for keep`: rows of opcodes a program never reaches are vacuous
  (`OpArm.of_unreached`), and premises are guarded by the kept opcodes.
- `whileMin` reaches 50 opcodes (`whileMinOps`). `whileMin_ops` and
  `whileMin_goodF1` now come from a2-sem's single shape run (`St.decodedOk`
  in `WhileMinShape.lean`); the separate `runToF1` kernel run is retired.
- `whileMin_halts_f1 (pre : F1PremisesFor (whileMinOps.contains ·) whileMin)`
  needs 16 fields:
  * proved by a2-sem's run: `extra`, `values`, `trapBounded`, `raises`;
  * open:
    - `row_CLOSURE`, `row_MAKEBLOCK`, `row_MAKEBLOCK2` (a1-arms);
    - `setglobal_barrier` (caml_modify, a6-gc);
    - `c_call{1,2,4}_{returns,effects}` (a1-arms/a1-prims);
    - `scratch` (MULINT/MODINT library scratch) and `modint_zero`.

**F1 assembly (2026-10-06)**
- `f1_table` (generated by `scripts/gen_f1_table.py`, drift-checked at a5):
  `Loaded Gc.f1Layout P c → GoodF1 P → Fits g1Budget P → F1Premises P →
  F1Arms P c (LoopAt Gc.f1Layout P)`. It dispatches all 134
  F1 opcodes to their rows; `F1Premises` collects the rows' program-level
  premises and the 15 rows still open (PUSHENVACC, GRAB, CLOSURE, CLOSUREREC,
  SETGLOBAL, MAKEBLOCK*, GETFIELD, SETFIELD*).
- `ocamlrun_refinement_F1_pinned` (the F1 statement for the pinned layout) and
  `whileMin_halts_f1` (the captured cut halts with "55\n2500\n36\n", exit 0),
  both from those premises (`F1Headline.lean`).
- `StackCapacity Gc.g1Budget` was false (8·3840 + 2·2048 = 34816 > 32768).
  a6-gc lowered the budget to 3584 stack words; `g1_capacity` is now proved.
- whileMin already has `ValuesInRange`, `BranchInts`, `ExtraBounded` and
  `TrapBounded`. Remaining whileMin premises: RaisesCaught, SwitchExotic,
  BinaryLibScratch, the DIV/MOD zero paths, FieldWriteReady, the C_CALL
  contracts, and the 15 open rows.

**Open / next** (2026-10-06, later)
- **Entry done for the pinned layout**: `f1_entry` (`EntryF1.lean`) takes
  `Loaded Gc.f1Layout P c` to a loop head representing `P.init`.
  * `LoadedAt` carries `caller` (InterpCaller) and `geometry` (ArmGeometry).
  * The closed whileMin witness fills them from a0-boot's
    `WhileMinCaller` and a6-gc's nursery geometry (`WhileMinLoaded.lean`).
  * `f1_entryStable`: entry's windows miss the F1 runtime footprint, after
    a6-gc carved out `caml_callback_depth`.
- **STOP row done**: `stop_row_f1 : GoodF1 P → OpArm P (LoopAt Gc.f1Layout P) .STOP`.
- Next: the F1 table assembly over a1-arms'/a2-sem's rows. C_CALL exit
  outcomes come through a1-arms' `CcallEffects` with a1-prims'
  `caml_sys_exit_halts`. Then `ocamlrun_refinement_F1_Statement Gc.f1Layout g1Budget`
  and the whileMin `Halts` (`whileMin_halts_of_arms` + `Gc.whileMin_loaded_f1`).

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
