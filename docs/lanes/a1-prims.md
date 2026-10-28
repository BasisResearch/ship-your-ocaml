# A1 F1 primitive summaries

## Counted fresh OO ID success and native C_CALL1 exit (2026-10-28)

Checked edits remain for lead review/integration in this worktree. Initial
HEAD `319f74d2` was clean. No other workers, Git metadata/landing-queue writes,
proof-budget changes, virtual-memory limits or generated-output hand edits
were used. The abstraction inventory ran before proof work.

`f1_counter_channelCountFrame` uses the original counted opened-list witness
to identify the selected `LibHeapAt` records. Their selected malloc bounds
place them above the actual static `oo_last_id` store. `CustomMemCall.owned`
from that same ledger places dynamic custom bytes in live blocks; the
existing static apartness confines low custom bytes to the resource word.
`accounting.frame` retains physical counts with the preserved Caml_state
word; `ChannelCountFrame.of_frame` retains natural refs, list links and head.
`counted_counterStable` pairs the count frame with `f1_counterStable`.

`counted_caml_fresh_oo_id_returns` runs `prim_caml_fresh_oo_id_returns` at
the local counted layout, reusing the adapter's explicit original-entry
count witness. Only semantic `world.ooId` changes, so the semantic channels
remain equal. The return adapter recovers counts at the native return's
actual placement through `ChannelCustomsRepr.at_geometry`.
`counted_fresh_oo_id_next` concludes the concrete counted successor from the
original C_CALL1 entry after real dispatch/setup/callee/suffix execution:
the accumulator is the old identifier and `world.ooId` is incremented.

`CcallExit.c_call1_halt` checks malformed/negative operands, absent primitive
slots and every real F1 primitive outcome. `counted_c_call1_halt` projects
`CountedLoopAt.toLoopAt` and consumes `ccall1Exit_pinned`, which runs actual
dispatch/setup and `caml_sys_exit_halts` through native exit to HTIF. Fits,
native headroom, saved registers, quiet exit globals and HTIF idleness are
the existing witnesses. The checked primitive model/native bridge covers
the unary integer argument, OS-result branches, status and console. Halt
has no successor count or placement obligation.
`counted_caml_sys_exit_returns` only excludes successful return; it does not
supply the halt. `counted_c_call1_row_of_next` composes this halt branch
with a future complete counted success branch using `ArmOutcome.of_cases`.
No extra runtime supplier or stronger GoodF1 is added.

The generated census separates `countedPrimSuccessCases` (**20 names**:
the existing 19 generic adapters plus the specialized unary fresh-id row)
from `countedPrimHaltCases` (**sys_exit only**). The exact nine names outside
this adapter are named registration, both descriptor openings, channel
listing, flush, output-char, output, output-bytes and format-int. The three
channel and four console summaries remain separately supplied; this census
does not reopen them. The complete-opcode census remains **132/134**.
Complete C_CALL1 still needs concrete opening/listing runtime producers and
composition of every remaining success/operand/outcome case. Complete
C_CALL2 still needs general format-int and named registration. Full F1
assembly and concrete physical runtime/startup producers remain open.
CustomMemCall remains named; six barrier rows retain exactly
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`
with G2; C4 round 2 waits for F1.

Validation:

- Row build passes **3,291 jobs**, `/tmp/counted-fresh-exit-rows3.log`:
  `lake build OCaml.Vm.Sim.CountedPrimRows OCaml.Vm.Sim.CountedControlRows`.
- Affected build passes **3,715 jobs**, `/tmp/counted-fresh-exit-affected.log`:
  all eight target modules plus CountedEntry, F1Table, WhileMinTable and
  CountedPrimAudit. The focused audit is emitted by the owning primitive
  generator, now importing CountedControlRows for the native halt branch.
- `python3 /tmp/counted-fresh-exit-check-audit.py` passes: exact membership
  of **77 focused reports**, coverage of **all nine new theorem declarations**,
  unique full-Audit registrations, and axioms contained in
  `{propext, Classical.choice, Quot.sound}` (or none). Regression reports
  include the pinned exit, actual native primitive halt, tagged status and
  OS-console preservation, existing counted setup/return consumers and the
  revised primitive remainder/census.
- Eleven generator drift checks pass: `gen_counted_prim_rows.py`,
  `gen_counted_control_rows.py`, `gen_counted_ccall2.py`, `gen_ccall_setups.py`,
  `gen_ccall_returns.py`, `gen_ccall_arms.py`, `gen_ccall_exits.py`,
  `gen_counted_stack_rows.py`, `gen_counted_alloc_rows.py`,
  `gen_counted_field_rows.py`, `gen_counted_console_audit.py` (all `--check`).
  Holes (**4,803 files**), discipline (**27 rules**), abstraction gate and
  `git diff --check` pass. Contract-route notes and the model simplification
  failure are recorded in DEAD-ENDS.md.
- Every Lean invocation first checked `free -g` (available ≥25 GB), then ran
  alone via `python3 scripts/lean-guarded.py --log /tmp/<task>.log --
  scripts/lean-capped.sh lake ...` under the inherited MemoryMax=12G and
  LEAN_NUM_THREADS=2. The guard stopped unsuccessful iterations. No
  heartbeat/recursion changes, new trusted axioms or full OCaml.Audit run.

The lead owns full Audit and landing via `scripts/integrate.sh`. Git metadata
and the landing queue are read-only here; checked edits are left for review.

## Actual counted console returns and complete C_CALL4 (2026-10-28)

Checked edits remain for lead review/integration. Initial worktree at
`004b521c` was clean; all work stays here. No workers, Git metadata writes,
proof-budget changes, generated-output hand edits or full Audit were used.

`ChannelRefsSame` names exactly equal list length and per-id refs.
`ChannelCustomsRepr.of_refs_same` transports all boundary counts; the model
custom-total equality is derived from those observations. `ConsoleCounts`
proves the observations from actual successful `writeFd`, closed/open flush,
room/full character output and all block-output fuel iterations, including
empty slices. Primitive inversions retain the real channel/int/slice/offset
checks and successful argument patterns. Chan, `primF1Impl`, `io.h` and the
actual `io.c` flush/output implementations were inspected. The failed
whole-chans/whole-record route and intermediate-update elaboration issue
are recorded in `DEAD-ENDS.md`.

`ChannelCountFrame.of_observations` permits mutable target buffer, offset
and cursor fields. `f1_console_channelCountFrame` uses the actual six
`consoleWindows` and the selected heap: opened-list uniqueness aligns frozen
count records with its real `chs`; malloc bounds separate statics/native
stack; recordsDisjoint separates every other record; the target refcount and
next offsets miss all three mutable record windows. `CustomMemCall.apart`
protects native/statics, `footprint` and `LibHeapAt.custom_apart_record`
protect the selected record through CustomSpace, and `accounting.frame`
transports the physical predicate with the preserved Caml_state word.
`counted_console_stable` pairs that complete count frame with the existing
`f1_console_stable`. The generic console native summaries retain their
ordinary payload/named/domain/native-save frames and target data proof.

`counted_prim_returns_of_refs` and `counted_refs_row` reuse that local runtime.
Existing unchanged-channel adapters specialize them. Actual callee returns
retain the frozen count observations, retarget through model refs/length,
then recover the returned placement with `ChannelCustomsRepr.at_geometry`.
Neither a matching placement nor a counted successor is presumed.

Four concrete counted primitive returns and their consumers are checked:

| Primitive | Arity | Actual counted consumer |
|---|---:|---|
| `caml_ml_flush` | 1 | `counted_flush_next` |
| `caml_ml_output_char` | 2 | `counted_output_char_next` |
| `caml_ml_output` | 4 | `counted_output_next` |
| `caml_ml_output_bytes` | 4 | `counted_output_next` |

`gen_counted_ccall2.py` now emits C_CALL2 and C_CALL4 from the same unary
composition/pattern; the arity-four instance reuses the existing native
prefix/argument loads, real `ccall1Log` setup frame and memory-preserving
suffix, with the actual return site and three popped stack arguments.
No new global runtime or stronger WindowStable supplier is introduced.
GoodF1, Fits, original readiness/reach/successor, heap and argument guards
remain unchanged.

Complete C_CALL4 is supplied separately from partial successes.
`primF1Impl_four_name` inspects every real primitive implementation pattern;
only output/output-bytes can return successfully at arity four.
`counted_c_call4_local_returns` uses their actual native contracts and
`PrimReturnsAtD.of_arity` for all other names. `counted_c_call4_refs` follows
all operand shapes, negative-index/stack-depth checks, missing slots, actual
F1 dispatch and primitive outcomes. The whole row reuses `c_call4_row`,
including its real setup/return execution, malformed/absent-slot rejection,
raise/callback exclusion and `CcallExit.of_arity`. The generated supported
census is **132/134**; comparison with HEAD preserves all 131 prior complete
row terms and adds exactly C_CALL4.

Exact remaining complete rows:

- C_CALL1: existing ordinary unary successes, three channel successes and
  flush now compose; concrete opening/listing runtime producers,
  fresh-oo-id and the actual unary sys_exit halt remain.
- C_CALL2: existing ordinary binary successes and output-char now compose;
  general format-int (including large-result allocation) and named
  registration remain.

Opening/listing, named registration, general formatting, concrete physical
runtime/startup suppliers and full counted F1 table assembly remain separate.
CustomMemCall remains named. Six barrier rows retain precisely
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`
with G2; C4 round 2 waits for F1. Complete C_CALL1 and C_CALL2 remain open.

Validation:

- Focused returns/consumers/whole-row build passes **2,372 jobs**:
  `lake build OCaml.Vm.Sim.CountedConsoleRows`,
  `/tmp/console-counts-rows3.log`.
- The affected build passes **3,713 jobs**: CountedControlRows,
  CountedPrimRows, CountedChannelRows, CountedEntry, F1Table and WhileMinTable,
  `/tmp/console-counts-affected.log`.
- `lake build OCaml.Vm.Sim.CountedConsoleAudit` passes **3,267 jobs** and
  **47 focused axiom reports**, `/tmp/console-counts-focused-audit.log`.
  `/tmp/console-counts-check-audit.py` verifies exact report membership,
  coverage of **all 36 new theorem declarations**, unique full-Audit
  registrations and axioms contained in
  `{propext, Classical.choice, Quot.sound}` (or none). The eleven regressions
  include unchanged-channel adapters, census/table terms and existing named
  primitive consumers. Full Audit is registered and left to the lead.
- Eleven relevant generator drift checks pass: native C_CALL
  setups/returns/arms/exits, counted stack/allocation/field/control/
  C_CALL2+4/primitive rows and the new focused console audit. A read-only
  comparison with HEAD confirms all 131 previous supplied row terms are
  unchanged and exactly C_CALL4 is added. Holes (4,802 files), discipline
  (27 rules), abstraction gate and whitespace checks pass.
- Every Lean launch checks `free -g` (available ≥25 GB), runs serially via
  `python3 scripts/lean-guarded.py --log /tmp/<task>.log --
  scripts/lean-capped.sh lake ...`, and retains the launcher's 12 GiB cap,
  two-thread setting and guard's failed/10 GiB stop. No virtual-memory
  limit, proof-budget change or generated-output hand edit was used.

Full `OCaml.Audit` and landing via `scripts/integrate.sh` remain the lead
gate. Git metadata and the landing queue are untouched.



## Previous arity milestone: counted C_CALL3/5 by F1 arity (2026-10-28)

Lead landing: `607536da` and the unchanged-proof module split `b83bf39e`
published in gate `004b521c` at 16:34 UTC, after the full 6,141-job build
and every integration stage passed. The 131-row census below is historical;
reviewed C_CALL4 above raises it to 132 at the next gate.

Checked edits are ready for lead review; no landing was attempted.
The initial worktree at `19b964fd` was clean. Read the binding briefs,
relevant lane/dead-end entries and abstraction inventory before proof work;
no workers, Git metadata writes or proof-budget changes were used.

Inspected all thirty `primsF1` names and every `primF1Impl` pattern.
`primF1Impl_wrong_arity` proves directly from those implementation patterns
that every argument count except 1, 2 or 4 evaluates to `.unsupported`.
`primF1Impl_arity` exposes the classification for any defined outcome;
it does not enumerate names or assume a successful return. In particular,
`caml_sys_exit` has the unary pattern and cannot halt at C_CALL3/5.
The primitive result equality rules out `.ok`, `.exit`, `.raise` and
`.callback` together, retaining `.unsupported` as the actual result. Existing
`PrimReturnsAtD.of_arity`/`prim_arity` cover successful returns; they stay
unchanged, with the theorem audited as a regression. The all-outcome lemma
supplies the required exit exclusion.

Shared `ccall_wrong_arity_step` handles all operand lists before either row
is instantiated. It follows stepI's combined negative-index/short-stack
guard and optional primitive lookup exactly. Out-of-range indices yield
`.wrong` via `opt none`; malformed operands, negative indices and short
stacks yield `.unsupported`. In the accepted-guard branch the real depth
fact proves `accu :: stack.take 2` has length 3 and
`accu :: stack.take 4` has length 5. `InF1.prim` supplies membership for
the selected name, so the real dispatcher reduces to `primF1Impl`.
`ccall_wrong_arity_row` uses the resulting `.unsupported`/`.wrong`
classification through `ArmOutcome` for any loop relation. GoodF1's
unchanged Good condition excludes both error constructors; no new
unreachability or native-return premise is used.

Generated `counted_c_call3_row` and `counted_c_call5_row` supply complete
`OpArm P (CountedLoopAt Customs f1Layout P)` terms without extra premises.
The generator installs those actual terms in `counted_supported_row` and
preserves all 129 previous terms. `counted_opcode_census`,
`counted_opcode_count` and `counted_remaining_count` now certify exactly
**131/134 supplied rows** and **three distinct open rows: C_CALL1/2/4**,
relative to the existing named custom and counted G2 suppliers.

Remaining complete-row obligations:

- C_CALL1: retain the existing nineteen-name adapter's unary successes and
  separate three channel successes; supply concrete opening/listing runtime
  producers, flush/fresh-oo-id effects and the actual unary sys_exit halt.
- C_CALL2: retain the three binary named successes; compose output-char,
  general format-int and named registration, including real semantic guards
  and native/runtime frames. Formatting includes the existing large-result
  allocation boundary.
- C_CALL4: compose both `caml_ml_output` and `caml_ml_output_bytes` with their
  four actual arguments, slice/channel/console guards and native effects.

Full counted F1 assembly and concrete runtime producers remain open.
`CustomMemCall` stays named and full remembered-table growth stays exactly
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`
with G2. GoodF1, the primitive table, custom physical meaning and capacity
are unchanged; C4 round 2 waits for F1.

Validation:

- Shared affected build: `lake build OCaml.Vm.Sim.CcallShort` passes
  **1,738 jobs**, `/tmp/ccall35-shared-final.log`; includes the shared
  semantic classification and operand helpers, with no new warnings.
- Final table build: `lake build OCaml.Vm.Sim.CountedControlRows` passes
  **3,184 jobs**, `/tmp/ccall35-rows-final.log`; checks both new whole rows,
  all 129 preserved supplied terms and the exact 131/3 census. No new warnings
  in the changed modules.
- `lake env lean -M 6000 -j 1 OCaml/Vm/Sim/CountedArityAudit.lean` passes
  **12 reports**, `/tmp/ccall35-focused-audit.log`. All use only
  `{propext, Classical.choice, Quot.sound}` or no axioms.
  `/tmp/ccall35-check-audit.py` verifies exact report membership/count,
  all six new theorem declarations and unique `OCaml/Audit.lean`
  registrations; the generated focus also covers the existing exit/arity
  helpers and all four census/table theorems.
- Ten relevant generator checks pass: native C_CALL setups/returns/arms/
  exits, counted stack/allocation/field/control/C_CALL2/primitive rows and
  their focused audit outputs. A read-only comparison with HEAD confirms
  every one of the 129 previous `counted_supported_row` terms is unchanged;
  exactly C_CALL3/5 are added. Hole, discipline, abstraction and whitespace
  checks pass. The refuted all-operands-unsupported candidate and list-match
  tactic route are recorded in `DEAD-ENDS.md`.
- Before every Lean launch, `free -g` showed available memory ≥25 GB.
  All builds/audits ran serially via `python3 scripts/lean-guarded.py --log
  /tmp/<task>.log -- scripts/lean-capped.sh lake ...`, retaining the inherited
  12 GiB/two-thread cap and the guard's 10 GiB stop. No virtual-memory limit,
  proof-budget change or generated-output hand edit was used.

Full Audit and landing via `scripts/integrate.sh` remain the lead gate.
Git metadata and the landing queue were left untouched.

## Previous named-success status

**2026-10-28 counted ordinary/allocating C_CALL continuation (base
`dfbaf165`): checked edits for lead review; no landing attempted.**

`CountedPrimReturnsAtR` now takes the original entry's complete
`ChannelCustomsRepr` explicitly, supplied by `CcallReady.of_counted_loop`.
Existing opening/listing return suppliers forget that additional input and
retain their existing successful-domain/native-runtime premises. The shared
`CountedPrimAdapter` transports readiness, setup and return layouts with equal
budgets, retaining every fetch, Fits/heap, reach/successor, geometry, argument,
allocation-placement and native-frame guard. It instantiates the ordinary
native summary at `countedLayout`; the actual callee post retains the frozen
counts, actual model channel equality retargets their world, and linked-list
uniqueness/total placement (`ChannelCustomsRepr.at_geometry`) recovers them at
the actual returned channel placement. Counts are never inferred from the
ordinary runtime or transported backwards from a callee post.

`counted_runtimeFrame` now frames the actual setup stores for both arities.
`counted_memoryStable` frames ordinary/read-only returns;
`counted_native_stable` uses the existing native window and selected count
frame for string inequality; `counted_primAllocFrame` handles the three Sys
allocations and `counted_allocFrame` handles int64-to-double. All reuse the
existing primitive return contracts without redoing instruction runs.
`gen_counted_ccall2.py` derives the binary counted setup/arm/success adapters
from the unary composition and consumes the existing native C_CALL2 prefix,
its actual `ccall1Log` and the existing suffix's memory equality. The binary
path retains the real combined index/stack guard, reads one existing stack
argument and drops it only in the suffix. `counted_c_call1_success` is reused
for unary cases. No arbitrary poststate or complete counted OpArm supplier is
introduced.

`CountedPrimRows` supplies **19 names: 16 unary, 3 binary**. Each generated
`counted_<name>_model` proves the exact successful arity and unchanged channels
from `primF1Impl`, including its real heap/argument guards. The names and
arities in `countedPrimCases` are:

| Native name | Arity |
|---|---:|
| `caml_sys_const_naked_pointers_checked` | 1 |
| `caml_sys_const_big_endian` | 1 |
| `caml_sys_const_word_size` | 1 |
| `caml_sys_const_int_size` | 1 |
| `caml_sys_const_max_wosize` | 1 |
| `caml_sys_const_ostype_unix` | 1 |
| `caml_sys_const_ostype_win32` | 1 |
| `caml_sys_const_ostype_cygwin` | 1 |
| `caml_sys_const_backend_type` | 1 |
| `caml_ml_string_length` | 1 |
| `caml_ml_bytes_length` | 1 |
| `caml_string_equal` | 2 |
| `caml_string_notequal` | 2 |
| `caml_sys_argv` | 1 |
| `caml_int_compare` | 2 |
| `caml_sys_get_config` | 1 |
| `caml_sys_executable_name` | 1 |
| `caml_sys_get_argv` | 1 |
| `caml_int64_float_of_bits` | 1 |

`counted_supported_c_call1_next` and `counted_supported_c_call2_next` conclude
`CountedLoopAt` through actual dispatch/setup/callee/suffix execution for
these names at their listed arities. `counted_prim_remaining_exact` checks
exactly **11/30 F1 names outside this new adapter**: the three unary channel
suppliers (`caml_ml_open_descriptor_out`, `caml_ml_open_descriptor_in`,
`caml_ml_out_channels_list`) retain their separately checked counted success
path and named runtime suppliers. The other eight remain outside the new
counted composition: `caml_ml_flush` (1), `caml_ml_output_char` (2),
`caml_ml_output` (4), `caml_ml_output_bytes` (4), `caml_format_int` (2),
`caml_register_named_value` (2), `caml_fresh_oo_id` (1), `caml_sys_exit` (1).
Those remaining arities describe the current model patterns, not new native
proofs. Successful return coverage does not cover exit behavior.

The opcode census remains **129/134 complete ordinary rows**, with exactly
**C_CALL1, C_CALL2, C_CALL3, C_CALL4, C_CALL5** still open as whole rows.
Nineteen new named success cases plus the three existing channel cases are
not a whole opcode table. Console effects, concrete channel opening/listing
runtime suppliers, formatter, named registration, fresh object-id counter
updates, exits, other arities and full counted F1 assembly remain separate.
`CustomMemCall` remains named; `BarrierGrowthFull` stays with G2 (including the
existing frozen counted-layout supplier); C4 round 2 waits for F1. GoodF1,
physical custom meaning, nursery capacity and semantic guards are unchanged.

Verification:

- `lake build OCaml.Vm.Sim.CountedPrimAdapter
  OCaml.Vm.Sim.CountedCcall1`: **2,344 jobs passed**,
  `/tmp/counted-prim-adapter.log` (initial entry/layout adapter).
- Final named-path build: **2,921 jobs passed**,
  `/tmp/counted-prim-rows4.log`, targets `CountedPrimRows` and
  `CountedChannelRows`; includes all nineteen model certificates, native
  adapters, both actual arities and existing channel successes.
- Final downstream affected build: **3,698 jobs passed**,
  `/tmp/counted-prim-affected-final.log`, explicit targets under
  `OCaml.Vm.Sim`: `ChannelReadiness`, `CountedCcall1`, `CountedCcallSetup`,
  `CountedChannelRows`, `CountedPrimAllocRows`, `PrimConstReturns`,
  `PrimStringEqualReturns`, `PrimStringNotequalReturns`, `CountedPrimRows`,
  `CountedEntry`, `F1Table`, `WhileMinTable`.
- `lake env lean -M 6000 -j 1 OCaml/Vm/Sim/CountedPrimAudit.lean`:
  **63 reports passed**, `/tmp/counted-prim-focused-audit.log`. Every one of
  the **52 new theorem declarations** is covered, together with changed
  channel/setup/success contracts and mandatory frame regressions. All
  reports use only `{propext, Classical.choice, Quot.sound}` or no axioms;
  all are registered exactly once in `OCaml/Audit.lean`.
  `/tmp/counted-prim-check-audit.py` checks exact report membership/count,
  declaration coverage, registrations and allowed sets. Full `OCaml.Audit`
  remains the lead gate.
- Ten generator drift checks pass: native C_CALL setup/return/arms, counted
  C_CALL2 and primitive rows/audit, counted allocation/control/field/stack,
  and F1 table. The two new checks are registered in check_all.sh stage a5.
  Holes (4,755 files), discipline (27 rules), abstraction gate (C4 stays 3)
  and `git diff --check` pass. Resolved interface/elaboration dead ends are
  recorded in `DEAD-ENDS.md`.

Every Lean launch ran alone through `python3 scripts/lean-guarded.py --log
/tmp/counted-prim-....log -- scripts/lean-capped.sh lake ...`, under the
inherited 12 GiB/two-thread policy (focused audit one thread), with `free -g`
checked first: available 89, 83, 88, 87, 87, 86 and 88 GB, all ≥25 GB. Early
binary/model elaboration failures were stopped by the guard and resolved at
unchanged limits. No heartbeat/recursion increase, virtual limit, generated
output hand edit, subagent, Git metadata write or landing-queue write was
used. All source changes stay in this worktree for lead review and landing
via `scripts/integrate.sh`.

**2026-10-28 counted write-row spatial supplier (base `9549edb8`):
checked for lead review; all affected builds and focused audits pass.**

Both prerequisites are present: the local `CustomSpace` repair (`2e47e2fc`)
and counted field/native-growth adapters (`9549edb8`). Inventory and binding
instructions were read before proof work. `LibHeapAt.refCustomApart` splits
actual `h.table.shape`: base zero is immediate; allocated storage's selected
arena bound excludes the static resource, `apartBlocks` excludes the domain
resource, and `h.customSpace.allocated` excludes table/backing bytes using the
actual nonzero remembered extent in `namedBlocked chs c`. Its end-minus-base
extent and strict storage size remain in the proof. `f1_refCustomApart`
exposes this at actual runtime states. Shared Covered membership alone is
still insufficient; the existing weak-interface alias obstruction is unchanged.

`f1_insert_channelCountFrame`, `counted_barrierRuntime` and all six barrier
row contracts now derive the extra spatial evidence from the selected heap.
No separate `RefCustomApart` supplier remains. Initially-empty growth still
uses the actual `GrowDone.kept`, selected ownership and forward count frame;
physical Customs, natural refcounts, list links and placement pass through
that same native run. OFFSETREF retains its actual object-field supplier.
The field/control generators emit complete SETGLOBAL, SETFIELD/0/1/2/3 and
OFFSETREF contracts, and the exact partial table contains **129/134** rows
relative to the named custom and counted G2 suppliers. Exactly **C_CALL1–5**
still lack whole-row contracts.

**Open G2 producer:** the six barrier contracts and partial table explicitly
retain `∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`.
It must supply physical Customs, natural references, list links and all
ordinary runtime/native fields at that frozen cp/world. The base-layout
contract is not lifted. No arbitrary whole-row premise, backward count
transport, GoodF1 restriction or physical-count change was added.
`CustomMemCall` stays named; concrete physical/startup/channel/custom-call
suppliers and full counted F1 assembly remain open. C4 round 2 waits for F1.

Verification:

- Guarded/capped `lake build OCaml.Vm.Gc.F1Heap OCaml.Vm.Gc.F1Barrier`:
  **1,558 jobs passed**, `/tmp/counted-spatial-heap.log`.
- Guarded/capped `lake build OCaml.Vm.Sim.CountedControlRows
  OCaml.Vm.Sim.CountedPrimAllocRows`: **3,200 jobs passed**,
  `/tmp/counted-spatial-rows.log`; includes the seven field rows,
  counted insertion/empty-growth adapters and exact 129/5 census.
- Final guarded/capped affected build: **3,664 jobs passed**,
  `/tmp/counted-spatial-affected-final.log`. Explicit targets:
  `Gc.{CustomLedger,F1Heap,F1Barrier,F1Grow}` and
  `Sim.{CountedRuntime,F1Growth,BarrierF1,CountedControlRows,
  CountedPrimAllocRows,CountedChannelRows,CountedEntry,F1Table,WhileMinTable}`
  under `OCaml.Vm`. This checks all affected native/count/startup/assembly
  consumers; full `OCaml.Audit` was left to the lead.
- Separate guarded/capped prerequisites pass: `OCaml.Vm.Sim.PrimMlOutput`,
  **1,908 jobs**, `/tmp/counted-spatial-mloutput.log`; and
  `OCaml.Programs.WhileMinShape`, **2,061 jobs**, kernel shape certificate
  39 seconds, `/tmp/counted-spatial-whilemin-shape.log`. No limits increased.
- Six field/control/stack/allocation/A2/F1 generator checks pass; hole check
  (4,750 files), discipline (27 rules), abstraction gate (C4 stays 3) and
  diff whitespace checks pass.
- Guarded/capped `lake env lean -M 6000 -j 1
  OCaml/Vm/Sim/CountedFieldAudit.lean`: **57 focused reports passed**,
  `/tmp/counted-spatial-focused-audit.log`. All axioms are within
  `{propext, Classical.choice, Quot.sound}` (or empty). Both new spatial
  theorems and all 15 new/changed theorem declarations are covered; every
  report is registered exactly once in `OCaml/Audit.lean`. Exact name/order,
  count, allowed-set, registration and declaration coverage are checked by
  `/tmp/counted-spatial-check-audit.py`; the corresponding names are in
  `/tmp/counted-spatial-{new-theorems,changed-theorems,audit-names}.txt`.
  Full Audit stays with the lead.

Every build/audit ran alone through `python3 scripts/lean-guarded.py --log
/tmp/counted-spatial-....log -- scripts/lean-capped.sh lake ...`, under the
inherited MemoryMax=12G and LEAN_NUM_THREADS=2 (focused audit: `-j 1`).
`free -g` was checked before every launch: available memory was respectively
74, 74, 73, 72, 91 and 87 GB (all at least 25 GB). No virtual-address limit,
heartbeat increase or direct generated-source edit was used.

Checked source edits remain in this worktree for lead review and landing via
`scripts/integrate.sh`. No subagents, Git metadata writes or landing attempt.
The earlier field/barrier entry below describes the superseded missing-supplier
boundary; the selected custom-space producer above closes that local gap.

**2026-10-28 counted field/barrier continuation (base `9de2d983`): checked
for lead review; six barrier rows retain the missing spatial supplier.**

`CountedRuntime` derives a real object-field channel/count frame from
`FieldWriteOk.of_geometry`, `F1HeapSafe.outside`, the entry's selected ledger
and `CustomMemCall.apart.covered`. `counted_fieldWriteReady` supplies the local
counted layout and retains the original stack budget. OFFSETREF is an object
field store. The existing ordinary native row is reused through `counted_row`.
`LoopGeometry.retarget` retains every geometry/placement field and transports
only an equal budget. The shared global/field call proofs now take actual
runtime/field frames; the original F1 specializations retain their interfaces.

`CountedBarrierFrame` derives the real struct/insertion windows from the
actual Table words. `LibHeapAt.insert_outside` supplies complete record/link
and static separation from `RefStorage.apartRecords` and the selected ledger.
The physical insertion frame and `counted_barrierRuntime` explicitly require
`∀ c, f1Runtime c → RefCustomApart c`. **That supplier is absent.** Ownership
of both ranges in H does not imply separation. `RefStorage.custom_alias` is a
checked conditional obstruction at the ledger/storage interfaces: given
aliased addressing observations, ownership remains true and separation fails.
It makes no reachable-alias or complete-runtime counterexample claim. No arbitrary WindowStable, counted
successor, new GoodF1 restriction or opaque whole-row premise is introduced.

The existing fast path composes at the counted layout using these frames.
`barrierGrowth_gprs_of_runtime` composes the actual initially-unallocated
path at an equal-budget layout while retaining the complete native post.
`CustomMemCall.owned`, `kept_covered` and actual `GrowDone.kept` supply physical
custom-state and live-record frames. `counted_barrierGrowth` has no insertion
separation premise. `f1_afterGrow_customApart` proves separation at that actual
fresh-allocation return from `GrowDone.disjoint` and `CustomLedger.owned`.
It does not establish a universal runtime supplier or custom-growth frame.

G2 must supply the existing named obligation at the stronger instantiation
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`.
Its output must retain physical Customs, natural channel refcounts and list
links for that frozen world/placement, all ordinary runtime/native fields and
budget/geometry. `BarrierGrowthFull f1Layout` alone does not supply it. No
additional opaque whole-row premise replaces this boundary.

`scripts/gen_counted_field_rows.py` generates seven real stepI channel facts,
OFFSETREF's supplied counted row, six conditional barrier row terms, their
conditional subtable/census and `CountedFieldAudit.lean`. The six terms require
both the missing spatial supplier and counted G2. They are deliberately
excluded from `countedOrdinaryOpcode`. The ordinary control generator's
exact census is **123/134 supplied counted rows**, with **eleven remaining**:

  `SETGLOBAL`, `SETFIELD0`, `SETFIELD1`, `SETFIELD2`, `SETFIELD3`, `SETFIELD`,
  `C_CALL1`, `C_CALL2`, `C_CALL3`, `C_CALL4`, `C_CALL5`.

Relative to the two explicit barrier suppliers, the six conditional terms
bring coverage to 129/134, with exactly C_CALL1–5 still lacking whole rows.
No full counted table closure or counted F1 assembly is claimed.
`CustomMemCall` remains named, `BarrierGrowthFull` stays G2 and C4 round 2
waits for F1. Physical startup/runtime, opening/listing and native custom-call
suppliers remain open. Checked source edits stay in this worktree for the
lead's review, full OCaml.Audit and integration; no Git metadata was written.

Verification:

- Guarded `lake build OCaml.Vm.Sim.CountedFieldRows`: **2,625 jobs, passed**
  (`/tmp/counted-field-frame7.log`). This checks all seven generated semantic
  facts/wrappers, both local counted frame instances and the actual initially
  unallocated growth frame, including its fresh custom-storage separation.
- Final affected build of `CountedControlRows`, `CountedPrimAllocRows`,
  `CountedChannelRows`, `CountedEntry` and `F1Table`: **3,631 jobs, passed**
  (`/tmp/counted-field-affected-final.log`). All supplied ordinary rows and
  inherited allocating opcode/primitive rows still check.
- Separate `WhileMinTable` build: **3,244 jobs, passed**
  (`/tmp/counted-field-whilemin-final.log`). Two earlier combined dependency
  builds were guard-stopped at 10 GiB, without a Lean proof error; sequential
  `PrimMlOutput` and `WhileMinShape` prerequisites passed (1,905 and 2,058 jobs;
  `/tmp/counted-field-mloutput.log`, `/tmp/counted-field-whilemin-shape.log`).
  The isolated kernel shape certificate took 118 seconds. No limits increased.
- Guarded `lake env lean -M 6000 -j 1 OCaml/Vm/Sim/CountedFieldAudit.lean`:
  **55 focused reports, passed**, with only `propext`, `Classical.choice`,
  `Quot.sound` or no axioms (`/tmp/counted-field-focused-audit.log`,
  `/tmp/counted-field-audit-check.txt`). All 48 added/refactored theorem
  declarations are covered, along with ordinary frame/allocation/census
  regressions (`/tmp/counted-field-declaration-check.txt`). All 55 reports
  are registered in `OCaml/Audit.lean`; full Audit was left to the lead.
- Nine final counted stack/allocation/control/field, A2 and F1 generator drift,
  discipline, hole and abstraction checks: **passed**
  (`/tmp/counted-field-static-checks.log`); `git diff --check` passes.
  The field row/audit generator is registered in check_all.sh stage a5.
- Every build/audit checked `free -g` first (available at least 25 GB), ran
  alone through `lean-guarded.py`/`lean-capped.sh` and retained the inherited
  12 GB scope and two-thread setting (the focused audit uses one Lean thread).
  No heartbeat increases, proof holes or direct generated-source edits.

The remaining blocker is an actual `RefCustomApart` runtime supplier,
including preservation across custom-storage changes. The stronger counted
`BarrierGrowthFull` remains the named G2 boundary. Checked source edits stay
uncommitted for the lead; no landing or full counted table closure is claimed.


**2026-10-28 local custom spatial migration: checked for lead review.**
The conditional pinned-domain record/frame obstruction is checked; both global
`CallerApart.records/named` laws are removed. Actual opening/listing and counted
frames consume selected ownership plus local `CustomSpace`. Full custom storage
ledgers and allocated-storage growth survive actual native returns, iterations
and epilogues; same-heap spatial/ownership evidence is exposed at return.
The final affected build passes 3,653 jobs and the 57-report allowed-axiom audit
covers all 23 new theorems. Full Audit/integration stay with the lead. Primitive
and counted-row totals are unchanged; GoodF1 is preserved. Physical accounting,
quietness, domain table-pointer input/frame, native `CustomMemCall` and concrete
runtime suppliers remain open, as detailed at the top of `a6-gc.md`.
`BarrierGrowthFull` stays G2; C4 round 2 waits for F1.

**2026-10-28 ordinary counted memory/control continuation (base `ed54de04`):
122/134 complete counted F1 row instances checked; lead integration pending.**

`scripts/gen_counted_control_rows.py` generates `CountedMemoryRows.lean`
(41 rows, including the existing CONST0/NEGINT) and `CountedControlRows.lean`
(16 control/raise/halt rows). These add 55 rows to the previous 67. Constants
and atoms, integer arithmetic/comparisons/branches, SWITCH, APPLY/APPLY1–3,
APPTERM/APPTERM1–3, RETURN, RESTART, CHECK_SIGNALS, STOP and all three explicit
raise opcodes reuse the existing checked native rows. `counted_memory_row`,
`counted_stack_row` and `counted_row` retain the ordinary guards and actual
GoodF1/Fits/capacity suppliers; no preservation premise or semantic guard was
added. RETURN keeps the original extra-count and saved-count use-site guards.

`counted_raiseRuntimeFrame` lifts the actual F1 `RaiseRuntimeFrame` using
`f1_stack_channelCountFrame`: VM writes use `CountStackWindow`, and
`NativeValid.headroom` places the real `nativeScratch` window above the
allocator arena. The channel-unlock hook comes from the entry base runtime.
Consequently DIVINT and MODINT reuse their complete ordinary rows, including
the caught zero-divisor native raise path and its GoodF1 caughtness proof.
The explicit raise family only needs the already lifted ordinary RuntimeFrame.

Channel semantics reduce actual `stepI`, exposing operand shapes using the
authoritative `gen_opcodes.nargs` before unfolding. SWITCH keeps the full
variable table tail. Shared `counted_enter_channels` covers apply, tail calls
and RETURN's apply path; `counted_raiseTo_channels`, `counted_intOp_channels`,
`counted_cmpOp_channels` and `counted_brOp_channels` factor the other operations.
The existing stack-row generator now accepts an optional semantic-operation
helper; its previous 58-row output and the allocation output remain current.

STOP uses the entry runtime's actual `Gc.f1_exitGlobals` and the loop's HTIF
idleness through generic `stop_row`. `counted_row` transports its halt
outcome directly; there is no successor count or stronger exit premise.

`counted_supported_row` supplies an actual complete `OpArm` for every true
entry of `countedOrdinaryOpcode`, using only the existing named custom
supplier plus GoodF1/Fits. `counted_opcode_census`, `counted_opcode_count` and
`counted_remaining_count` check the exact complement against
`Opcode.fragment = .F1` (the authoritative F1 opcode domain), 122 supported
opcodes and twelve distinct remaining obligations:

  `SETGLOBAL`, `SETFIELD0`, `SETFIELD1`, `SETFIELD2`, `SETFIELD3`, `SETFIELD`,
  `OFFSETREF`, `C_CALL1`, `C_CALL2`, `C_CALL3`, `C_CALL4`, `C_CALL5`.

OFFSETREF writes a represented object and is excluded from these memory/stack
frames. Allocating/barrier extensions and effectful primitive-call summaries
remain with their separate tasks; the seven previously checked nursery rows
are only reused in the partial table/census. Successful named C_CALL cases do
not close any complete C_CALL opcode row. No full counted `F1Arms` assembly
is claimed. `CustomMemCall` remains named; physical startup/runtime suppliers,
channel opening/listing suppliers and the existing allocation/GC boundaries
remain explicit. `BarrierGrowthFull` stays with G2; C4 round 2 waits for F1.

Verification:

- Guarded final affected build of `CountedControlRows`, `CountedChannelRows`,
  `CountedEntry` and `CountedPrimAllocRows`: **3,494 jobs, passed**
  (`/tmp/counted-control-final-build.log`). This checks generated memory/control
  rows, the inherited stack/allocation rows and counted entry/channel regressions.
  No new warnings in CountedRuntime/CountedMemoryRows/CountedControlRows.
- Guarded `/tmp/counted-control-focused-audit.lean`: **130 reports, passed**;
  only `propext`, `Classical.choice`, `Quot.sound` or no axioms
  (`/tmp/counted-control-focused-audit.log`,
  `/tmp/counted-control-audit-check.txt`). All 122 newly introduced theorem
  reports are registered in `OCaml/Audit.lean`; the focus also rechecks the
  two inherited memory rows and six existing frame/entry/channel boundaries.
- Counted control/stack/allocation, A2 and F1 table generator drift checks,
  proof discipline (27 rules), hole check and abstraction gate: **passed**.
  The control generator is registered in `check_all.sh` stage a5.
- Every build/audit checked `free -g` first (available at least 25 GB) and
  ran alone through `lean-guarded.py`/`lean-capped.sh`, within the inherited
  12 GB scope and two-thread limit. No increased proof budgets.

The lead owns full `OCaml.Audit` and commits/landing via `scripts/integrate.sh`;
this worktree leaves checked source edits uncommitted for review.

**2026-10-27 counted nursery/native allocation: checked for lead review and
integration.** Started at committed HEAD `648afc4a`, with the checked counted
stack frame. Read `CLAUDE.md`, the A1 plan/status and this log's remaining-row
list plus `DEAD-ENDS.md`; ran `scripts/abs_inventory.sh` before proof work.
No workers/subagents, Git metadata edits, commits or landing actions.

`f1_channelCountFrame` factors the selected-ledger argument out of the checked
stack frame; `f1_stack_channelCountFrame` reuses it. The entry's actual
`LibHeapAt`, `OpenChannels.unique`, and `F1HeapSafe.outside` preserve whole
channel records (refcounts and next links) and the static opened-list head.
The frozen counted placement may differ from the nursery geometry's placement;
no placement-equality premise or independent address separation was added.

`CountedAllocFrame.lean` proves `CountAllocWindow` static/live-block/custom-state
separation for caller windows, the actual free nursery, `young_ptr` and
`local_roots`. Custom-state separation comes from `CustomMemCall.apart`;
physical counts come from `accounting.frame`. `f1_alloc_channelCountFrame`
reflects the actual log into windows, reuses `ChannelCountFrame.of_frame`, and
transports the observations to total-byte native posts. `counted_allocFrame`
lifts the real reservation/body log, including CLOSUREREC's VM-stack stores;
`counted_primAllocFrame` lifts the existing native primitive log and final-young
geometry contract. No stronger `WindowStable`/`AllocationRuntime` or counted
successor is assumed. The only named custom supplier remains `CustomMemCall`.

`counted_alloc_row` reuses `counted_row`, `counted_runtimeFrame` and the actual
allocation/memory frames at `countedLayout f1Layout`. Its local budget is the
existing F1 budget. The arbitrary-layout supplier route loses that budget
agreement and is recorded as an interface dead end in `DEAD-ENDS.md`.
`scripts/gen_counted_alloc_rows.py` generates seven instances: MAKEBLOCK,
MAKEBLOCK1/2/3, CLOSURE, CLOSUREREC and GRAB. All native execution and existing
GoodF1/Fits/capacity guards come from the ordinary rows. Shared generator
`channel_certificate` exposes operand shapes (including CLOSUREREC's variable
offset list), then reduces actual `stepI` branches for unchanged channels.
The old stack generator output is byte-for-byte unchanged. The new generator
is registered in `check_all.sh`.

Checked every `PrimAllocFrame` use site: get-config requires that frame;
executable-name and get-argv additionally require `ExeNameAt`. The existing
`f1_exeNameAt` producer projects from the base runtime, so `CountedPrimAllocRows`
instantiates all three `PrimReturnsAt` summaries at the local counted layout.
These are callee return contracts, not complete counted C_CALL opcode rows.
The separate int64-float conversion uses `AllocFrame` and is not instantiated
here. Console/counter/native frames for other primitives are not assumed for
the stronger predicate.

Validation:

- Guarded affected build of `CountedAllocRows`, `CountedPrimAllocRows`,
  `CountedStackRows`, `CountedChannelRows`, `CountedEntry` and `F1Table`:
  **3,626 jobs**, passed (`/tmp/counted-allocation-rows1.log`); final generated
  row cleanup checked with the same targets and **3,626 jobs**, passed
  (`/tmp/counted-allocation-rows2.log`). No new allocation-module warnings.
  The shared frames passed separately, **2,004 jobs**
  (`/tmp/counted-allocation-frame3.log`).
- Guarded `/tmp/counted-allocation-focused-audit.lean`: **32 reports**,
  including all **27 new theorems** and five stack-frame/row regressions,
  passed. Only `propext`, `Classical.choice`, `Quot.sound` occur
  (`/tmp/counted-allocation-focused-audit.log`,
  `/tmp/counted-allocation-audit-check.txt`). All new reports are registered
  in `OCaml/Audit.lean`; full Audit remains the lead gate.
- Counted allocation/stack and F1 table generator drift checks, hole check
  (4,741 files), discipline (27 rules), abstraction gate and diff checks pass.
  C4 remains at 3. Generated files were produced by their generators.
- Every Lean invocation checked `free -g` first (available ≥25 GB) and used
  `python3 scripts/lean-guarded.py --log /tmp/... -- scripts/lean-capped.sh lake ...`.
  One build at a time under the inherited 12 GB scope and two-thread limit;
  no virtual-memory limit or increased proof budget.

**Precise remaining counted-opcode list:** 67/134 ordinary counted F1 rows
are supported (the previous 60 plus seven allocating rows). These **67** still
lack complete counted `OpArm` instances:

  `APPLY`, `APPLY1`, `APPLY2`, `APPLY3`, `APPTERM`, `APPTERM1`, `APPTERM2`, `APPTERM3`, `RETURN`,
  `RESTART`, `SETGLOBAL`, `ATOM0`, `ATOM`, `SETFIELD0`, `SETFIELD1`, `SETFIELD2`, `SETFIELD3`, `SETFIELD`,
  `BRANCH`, `BRANCHIF`, `BRANCHIFNOT`, `SWITCH`, `BOOLNOT`, `RAISE`, `CHECK_SIGNALS`, `C_CALL1`, `C_CALL2`,
  `C_CALL3`, `C_CALL4`, `C_CALL5`, `CONST1`, `CONST2`, `CONST3`, `CONSTINT`, `ADDINT`, `SUBINT`, `MULINT`,
  `DIVINT`, `MODINT`, `ANDINT`, `ORINT`, `XORINT`, `LSLINT`, `LSRINT`, `ASRINT`, `EQ`, `NEQ`, `LTINT`,
  `LEINT`, `GTINT`, `GEINT`, `OFFSETINT`, `OFFSETREF`, `ISINT`, `BEQ`, `BNEQ`, `BLTINT`, `BLEINT`,
  `BGTINT`, `BGEINT`, `ULTINT`, `UGEINT`, `BULTINT`, `BUGEINT`, `STOP`, `RERAISE`, `RAISE_NOTRACE`

C_CALL obligations remain: compose the three new allocating return contracts
through actual setup/callee/suffix into `CountedLoopAt`, with their unchanged
channel semantics and selected-placement recovery; supply the other primitive
frames/returns; handle other arities, exits and full opcode outcome cases.
The three existing unary channel success paths still use their real named
opening/listing suppliers and do not close the whole C_CALL1 row. Complete
C_CALL1–5 rows and full `F1Arms` assembly remain open. No counted successor or
stronger runtime frame was added as a supplier.

Still explicit: complete physical custom runtime/startup zero and the named
custom machine supplier, concrete channel opening/listing runtime/heap/ledger/
pin and after-call suppliers, barriers and GC-capable allocation, effectful
channel calls, named registration/general formatting, and reset reachability.
`BarrierGrowthFull` stays with G2; C4 round 2 waits for F1. `GoodF1` and its
nursery allocation domain are unchanged. Full `OCaml.Audit` and integration
remain the lead gate; checked edits are left uncommitted for review. The lead
commits and lands with `scripts/integrate.sh`.


**2026-10-27 counted stack RuntimeFrame and 58 row instances: checked for lead
review/integration.** Started at clean committed HEAD `2ee3051b`, after the
counted-loop continuation (`274e994b`) and its allocator-entry follow-up
(`16da258b`). Read its final remaining-obligation list, `CLAUDE.md`, relevant
`PHASES.md`/`PLAN.md`, and `DEAD-ENDS.md`; ran `scripts/abs_inventory.sh`
before proofs. No workers/subagents, Git metadata edits or landing actions.

`ChannelCountFrame.of_frame` carries complete physical counts, natural
refcounts and next links through window frames. `CountStackWindow` includes
only VM stack windows, the existing four `vmDomainOffsets`, and native
stack windows above the allocator arena. `f1_stack_channelCountFrame` obtains
the **entry's own** `LibHeapAt` from `f1Runtime`; `OpenChannels.unique`
identifies that ledger's opened list with `placedChannels cp world.chans.length`.
`F1HeapSafe.outside` then derives record separation and bounds from actual
live allocations. No independent channel-address assumption, matching return
placement premise or frozen footprint is needed. The named
`CustomMemCall.accounting.frame` and `CallerApart` prove physical-state
preservation, including the existing domain-resource exception and native
stack separation. Static head and `Caml_state` readbacks also survive.

`counted_runtimeFrame` lifts **every** `RuntimeFrame` field at `countedLayout`;
its `windows` field uses that proved complete frame. `counted_row` factors
the old memory-row adapter and retains `countedRunning_of_counts` placement
coherence. `counted_stack_row` supplies both the actual lifted frame and
`counted_memoryStable`. No global runtime strengthening or extra `GoodF1`
guard was added; the real counted C_CALL setup/callee/return path is retained.

`scripts/gen_counted_stack_rows.py` generates `CountedStackRows.lean` and
is registered in `check_all.sh`. Its **58 rows** reuse the existing generic
native proofs: PUSH/PUSHACC0–7/PUSHACC, ASSIGN, PUSHENVACC1–4/PUSHENVACC,
PUSHGETGLOBAL/PUSHGETGLOBALFIELD, PUSHATOM0/PUSHATOM,
PUSHCONST0–3/PUSHCONSTINT, PUSHOFFSETCLOSUREM3/0/3/general, PUSH_RETADDR,
PUSHTRAP/POPTRAP; ACC0–7/ACC, POP, ENVACC1–4/ENVACC, GETFIELD0–3/GETFIELD,
GETGLOBAL/GETGLOBALFIELD, OFFSETCLOSUREM3/0/3/general. Fits, reachability,
geometry and all use-site guards are inherited from those proved rows;
`g1_capacity` supplies the actual capacity. Traps use exactly the same frame.
Allocation and barrier effects are outside it.

Validation:

- Guarded build of `CountedStackRows`, `CountedMemoryRows`,
  `CountedChannelRows`, `CountedEntry`: **3,194 jobs**, passed
  (`/tmp/counted-stack-rows4.log`); the shared frame also passed separately
  (`/tmp/counted-stack-frame3.log`, 1,540 jobs).
- Guarded `/tmp/counted-stack-focused-audit.lean`: **137 reports**, passed,
  including all **123 new theorems**, earlier memory rows, placement coherence,
  counted channel execution and the concrete counted entry. Only `propext`,
  `Classical.choice`, `Quot.sound` occur (`/tmp/counted-stack-focused-audit.log`,
  `/tmp/counted-stack-audit-check.txt`). All new reports are registered in
  `OCaml/Audit.lean`; the full Audit remains the lead gate.
- Push/ACC/field/a2/count-stack generator drift checks, hole, discipline,
  abstraction and diff checks pass; C4 remains at 3. Generator operand shapes
  reuse `gen_opcodes.nargs`; no generated output was hand edited.
- Each Lean invocation used `free -g` first (available ≥25 GB), then
  `python3 scripts/lean-guarded.py --log /tmp/... -- scripts/lean-capped.sh lake ...`.
  One build at a time in the inherited 12 GB scope with two threads; no
  virtual-memory limit or increased proof budget.

**Precise remaining counted-opcode list:** 60 of 134 F1 opcodes now have
ordinary counted rows (these 58 plus CONST0/NEGINT). The following **74**
still lack complete counted `OpArm` instances:

  `APPLY`, `APPLY1`, `APPLY2`, `APPLY3`, `APPTERM`, `APPTERM1`, `APPTERM2`, `APPTERM3`, `RETURN`,
  `RESTART`, `GRAB`, `CLOSURE`, `CLOSUREREC`, `SETGLOBAL`, `ATOM0`, `ATOM`, `MAKEBLOCK`, `MAKEBLOCK1`,
  `MAKEBLOCK2`, `MAKEBLOCK3`, `SETFIELD0`, `SETFIELD1`, `SETFIELD2`, `SETFIELD3`, `SETFIELD`, `BRANCH`, `BRANCHIF`,
  `BRANCHIFNOT`, `SWITCH`, `BOOLNOT`, `RAISE`, `CHECK_SIGNALS`, `C_CALL1`, `C_CALL2`, `C_CALL3`, `C_CALL4`,
  `C_CALL5`, `CONST1`, `CONST2`, `CONST3`, `CONSTINT`, `ADDINT`, `SUBINT`, `MULINT`, `DIVINT`,
  `MODINT`, `ANDINT`, `ORINT`, `XORINT`, `LSLINT`, `LSRINT`, `ASRINT`, `EQ`, `NEQ`,
  `LTINT`, `LEINT`, `GTINT`, `GEINT`, `OFFSETINT`, `OFFSETREF`, `ISINT`, `BEQ`, `BNEQ`,
  `BLTINT`, `BLEINT`, `BGTINT`, `BGEINT`, `ULTINT`, `UGEINT`, `BULTINT`, `BUGEINT`, `STOP`,
  `RERAISE`, `RAISE_NOTRACE`.

`C_CALL1` in that list already has successful counted execution for the three
channel primitives under their real named opening/listing runtime suppliers;
it is not a complete opcode row. The 74 include straightforward remaining
memory-only adapters as well as allocation/barrier/control/primitive effects;
this list makes no claim that all require a new frame.

Still explicit: complete physical custom runtime/startup zero (table
occupancy alone is insufficient), the named `CustomMemCall` machine supplier,
allocation/barrier rows and other effectful primitives, counted other call
arities, full `F1Arms` assembly, concrete opening/listing runtime/heap/record/
named-ledger and after-call suppliers, named registration, general formatting
and reset reachability. `BarrierGrowthFull` stays with G2; C4 round 2 waits
for F1. Checked edits remain uncommitted for lead review and integration.


**2026-10-27 counted loop continuation: checked partial work for lead review;
headline open.**

Prerequisite `71547e46` is committed (HEAD at start `cfbc61ef`, clean
worktree). Its final remaining-obligation list, `CLAUDE.md`, the A1 sections
of `PLAN.md`/`PHASES.md` and `DEAD-ENDS.md` were read before editing, and
`scripts/abs_inventory.sh` was run. No worker/subagent was started.

`CountedInvariant` supplies `CountedLoopAt` for the already arbitrary-relation
`F1Arms` assembly. A shared coherence proof uses `OpenChannels.unique` and
total channel placement to show that the opened list determines every valid
channel address. `ChannelCustomsRepr.at_geometry` and
`countedRunning_of_counts` therefore attach framed counts to an ordinary
producer's own stack witness. They retain the independent physical count;
they do not infer it from the refcount total or from the old runtime invariant.

`countedLayout` is a local runtime extension for one non-channel row.
`counted_memoryStable` proves its actual count frame via
`ChannelCountFrame.sameMemory`; `counted_memory_row` then reuses generic
opcode proofs unchanged, recovering the selected channel placement through
the coherence theorem. `counted_const0_row` and `counted_negint_row` are
the first ordinary counted rows on this route. There is no global change
to `Layout`, `VmReprAt` or the `GoodF1` domain, and no new assumed row-result
or count-preservation field.

The entry execution now exports `EntryLoopPost` through
`entry_loopAt_framed`; its ordinary API projects the same execution.
`EntryFrame.customCountFrame` proves the physical frame from the existing
named `CustomMemCall` footprint, including native stores, callback-depth
and external-raise stores. `counted_entry_of_custom` carries any complete
startup accounting witness through that actual prologue.

The layout generator measures custom-table element size and base/pointer
offsets. The startup-read generator certifies the actual empty table's
pointer and its zero base/insertion words. `ChannelCustomCount` is an
independent **table-occupancy component**, with checked uniqueness, byte
framing and startup zero. `whileMin_counted_entry` carries that component
through the real interpreter entry. The lead integrated the closed cut
allocator certificate and removed the former heap premise. It is **not** a complete physical `Customs` instantiation for the
custom machine premise: GC resource accumulators and the current domain's
custom-table pointer still need their full runtime invariant and producers.
Occupancy alone is not used to derive readiness; this limitation is recorded
in `DEAD-ENDS.md`. `table_count_resources_unconstrained` is a checked contract
obstruction: every major-resource word is compatible with the same table
occupancy. It makes no reachability claim.

`CcallReady.of_input` factors the ordinary placement producer.
`CcallReady.of_counted_loop` selects its channel placement from the counted
stack, while the shared producer extends only the heap placement.
`counted_c_call1_success` derives the actual reachable successful successor,
applies its `Fits` bound and composes dispatch/setup/callee/return into
`CountedLoopAt`. `counted_channel_c_call1_next` supplies the existing real
counted opening and out-list summaries on that execution. It accepts exactly
the existing runtime/heap/footprint suppliers, not an assumed counted
primitive or opcode result. Complete `ChannelCustomsRepr` survives the suffix.

The lead merged the closed allocator certificate and both boot-read additions.
The updated `whileMin_counted_entry` has no heap premise; the combined check
passes 3,649 jobs and all 39 focused audits (`/tmp/syo-counted-allocator-assembly.log`,
`/tmp/syo-counted-allocator-audit.log`). Generator drift also passes.

**Remaining before ordinary F1 assembly can consume this path:**

- A complete physical custom-runtime predicate and its actual startup zero,
  including resource accumulators/table identity, with the accepted named
  `CustomMemCall` supplier for its real counted returns. The checked table
  occupancy component does not discharge this supplier. The current
  `CallerApart.domainField` admits only `extra_heap_resources_minor`;
  table-pointer identity needs its own actual pin/frame or a corrected
  footprint and producers, not an implicit old-frame consequence.
- Lift the remaining generic rows using actual frames. Memory-writing rows
  need lifted `RuntimeFrame`/allocation/barrier instances from physical
  footprint separation; non-custom primitive summaries must retain physical
  counts, refcount observations and links across their actual effects.
  CONST0/NEGINT alone do not preserve the invariant for a whole F1 loop.
- Integrate all counted C_CALL branches (including non-custom primitives
  and other arities) and all ordinary rows into `F1Arms` at `CountedLoopAt`.
  Existing `f1_table`, `F1CcallOpen`, `WhileMinOpen` and the headline remain
  at their original ordinary relation and retain their channel fields.
- Opening `OpenOutRuntimeAt.after`; out-list selected heap/record/named
  ledger entry geometry and after-call runtime pins; named registration,
  general formatting, and reset reachability remain open; captured `libHeap`
  is now certified separately. `BarrierGrowthFull`
  stays with G2 and C4 round 2 waits for F1.

Validation passes:

- The guarded affected build of `OCaml.Vm.Sim.CountedEntry`,
  `OCaml.Vm.Sim.CountedChannelRows`, `OCaml.Vm.Sim.CountedMemoryRows`,
  `OCaml.Vm.Sim.F1Ccall` and `OCaml.Vm.Sim.WhileMinTable`: **3,694 jobs**
  (`/tmp/counted-loop-checked-build2.log`). The physical-count/startup module
  also passed its initial 1,301-job build.
- Guarded `lake env lean /tmp/counted-loop-focused-audit.lean`: **39 reports**,
  all using only `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/counted-loop-focused-audit.log`, checked by
  `/tmp/counted-loop-audit-check.txt`). All 32 new theorem reports and the
  existing compatibility/downstream reports are registered in `OCaml/Audit.lean`.
  The executable-name return observation now applies the existing
  `copyMemory_eq` through `congrFun`, matching the shared `copyMemoryAt`
  post; its entry and primitive reports are included.
- Layout/runtime-read/F1-table generator drift, hole, discipline, abstraction
  and diff checks pass; C4 remains at 3.

All Lean invocations used `python3 scripts/lean-guarded.py --log /tmp/... --
scripts/lean-capped.sh lake ...`, with `free -g` beforehand (available memory
at least 25 GB), one build at a time, the inherited 12 GB scope and two
threads. No proof budget was increased or virtual-memory limit added.
Git metadata and the integration queue remain untouched; checked edits are
uncommitted. Full `OCaml.Audit`, review, commit and landing belong to the lead.
The task remains **stuck at complete startup custom-runtime accounting and
the remaining ordinary/count-preserving frame/row producers for F1 assembly**.

**2026-10-27 initialized-string native return (bprime): checked for lead review.**
`InitializedString.initialized_string_nursery` proves the actual
`caml_alloc_initialized_string` nursery entry-to-return at `0x8000c284`,
reusing the nursery allocator and complete memcpy through generated real
save/call/return boundaries. Data-only inputs admit the formatter's caller
stack buffer; source bytes and saved words follow through actual stores.
Shared StringCopy laws retain full byte-object/padding and native/output/byte
frames. `AllocSprintfLong.short_initialized` composes the real continuation
from `0x80013f10` back to `0x80013f20`; the local length ≤20 supplies the
nursery size branch. The complete formatter prologue/wrapper/original return,
reachable runtime/locale/ownership suppliers and C_CALL2 remain open, as do
general GoodF1 formatting and its major-result route. The affected build
passes (1,403 jobs), as do all 81 focused allowed-axiom reports; 63 audits are
newly registered. Generator drift, hole, discipline and abstraction gates pass.
Checked edits await lead review/commit/integration; full Audit is the lead gate.
Detailed validation and remaining suppliers: `docs/lanes/bprime.md`.


**2026-10-27 complete counted channel returns: checked for lead review/integration.**

Started from checked HEAD `13320f38` with a clean worktree, after reading the
previous worker's remaining-obligation list and `DEAD-ENDS.md`. The abstraction
inventory was run before proof work. `CountedCcallReturnAt` strengthens the
actual machine post with full `ChannelCustomsRepr` at its own `ChanPlace`;
`CountedCcallReturn.placed` packages that same ordinary/count witness. Both
open-descriptor adapters reuse `open_out_counts` from their actual `OpenedOut`
return. No second unrelated post or universal count implication is assumed.

`WalkAt.refwords` tracks the visited listed portion once. `OpenChannels.nodup`
uses finite-chain suffixes and `OpenChannels.unique` to justify one visit per
record. `ListedStep.refwords` reads the actual four-byte native SW through
`word32_writeLog`, then frames every record's field through the named custom
call and cons allocation. This includes unvisited and unlisted records.
`OutListReturned.refwords` retains those observations through the native
prologue/epilogue. `out_list_counts` converts the machine words to natural
counts using the successful successor's `Fits`/customs bound (`quietBound = 5`)
to rule out wrap. The physical batch count still comes independently from
`CustomMemCall`'s exact actual machine post, never from a transient refcount sum.

The return generator now retains `PlacedRunning` in `_return_framed`, exposing
the placement used by the ordinary return. The ordinary interfaces remain
projections. `counted_c_call1_arm` uses `dispatch_compose`/`callSeg` for the same
dispatch/setup/callee/suffix run and `ChannelCountFrame.sameMemory` for its
suffix. Its result is `CountedRunning`, with `CountedVmReprAt` and geometry at
that final placement, rather than only `CountedResult.physical`.

Remaining obligations outside this return-boundary task:

- Startup: select the concrete physical `Customs` predicate and establish its
  actual zero witness. `f1_channelCounts_of` still consumes that witness and
  the checked empty-list head. Carry counted representation through
  `LoadedAt`/entry into the selected ordinary loop-stack placement.
- Ordinary loop preservation: strengthen `Running.stack`/`LoopAt` and the
  shared payload/opcode producers to retain counts at their own placements;
  prove `ChannelCountFrame` through non-channel opcodes and ordinary
  non-custom primitive summaries; integrate counted entries/returns into the
  F1/whileMin tables. The actual unary setup and unary return are handled;
  counted composition of other call arities remains separate work.
- Runtime suppliers: concrete `CustomMemCall` (accounting uniqueness, frame,
  readiness, footprint and exact machine counter transition), opening
  `OpenOutRuntimeAt.after`, and out-list selected heap/record/named-ledger
  entry geometry and after-call runtime pins stay explicit and open.
- Named registration, general formatting and reset/libHeap closure remain
  open. `BarrierGrowthFull` stays G2; C4 round 2 waits for F1. No new model
  guard or `GoodF1` restriction was added.

Validation passes:

- `scripts/lean-capped.sh lake build OCaml.Vm.Sim.OutListRun
  OCaml.Vm.Sim.OutListAdapter OCaml.Vm.Sim.OpenOutReturn
  OCaml.Vm.Sim.CountedCcall1 OCaml.Vm.Sim.F1Ccall
  OCaml.Vm.Sim.WhileMinTable`: **3,687 jobs**
  (`/tmp/channel-boundary-checked-build.log`), including `OutListWalk`, all
  five generated suffixes, both opening adapters and the out-list boundary.
- `scripts/lean-capped.sh lake env lean /tmp/channel-boundary-audit.lean`:
  **31 reports**, including all eight new theorems and the five framed suffixes
  with their compatibility projections. Every report uses only `propext`,
  `Classical.choice`, `Quot.sound`; all are registered in `OCaml/Audit.lean`
  (`/tmp/channel-boundary-audit.log`, checked by
  `/tmp/channel-boundary-audit-check.txt`).
- Hole, discipline and abstraction gates pass (C4 remains at 3). The changed
  return generator, setup generator and F1 table generator all pass `--check`;
  `git diff --check` passes.

Each Lean invocation used the capped wrapper with `free -g` beforehand
(available memory exceeded 25 GB), one build at a time and the inherited
12 GB/two-thread policy. Default-budget normalization failures were repaired
with `enter_refword`/`word32_writeLog` and the existing `ProKept.bytes` frame;
these routes are recorded in `DEAD-ENDS.md`. Final checks pass without
increasing budgets or adding trust primitives. Generated suffixes were changed
only through their generator. No subagent, virtual-memory limit, Git metadata
or integration-queue write was used.

The requested channel return/refcount producer and actual unary return are
closed **conditionally on the existing named runtime suppliers**. The startup
and ordinary non-channel invariant obligations above remain open. Checked
edits are uncommitted for lead review; full `OCaml.Audit`, commit and
`scripts/integrate.sh` landing remain the lead gate.


**2026-10-27 actual unary C_CALL setup/suffix: partial continuation of
`dc8035a8`, for lead review. The ordinary F1 loop is still open.**

The prerequisite custom-count checkpoint was committed at `dc8035a8`; its
remaining-obligation list above the earlier validation was inspected before
editing. The worktree started clean. The shared abstraction is
`ChannelCountFrame`: its physical transition, natural refcount observations
and opened-list links reconstruct all of `ChannelCustomsRepr`. Its `of_log`
uses the existing whole-record payload separation and
`outLRange_subrange`/`bytesT_writeLog_out`; `sameMemory` reuses
`CustomAccounting.sameMemory`.

The setup/return generators now retain exact effects in
`c_call{1..5}_setup_framed` and `c_call{1..5}_return_framed`; the original
interfaces are projections. `Ccall1WriteOk.customCountFrame` proves physical
state separation from `CustomMemCall.apart.covered`/`.domainField`, the
existing stack reserve and the actual setup log. `counted_c_call1_setup`
therefore produces a complete `CountedCcallSetupPost` on that generated
execution, with no new count-preservation supplier. From that actual setup,
`counted_c_call1_setup_ready` consumes the reachable successful successor's
`Fits` bound and its semantic charge (`openChan_customs` or
`listRefs_customs`). No readiness is inferred from a pending refcount store.

`counted_c_call1_arm` uses `dispatch_compose` and `callSeg` to compose this
setup, the existing counted callee summary, and the generated suffix. It
retains the callee's actual physical successor count across the suffix's
memory equality. Its conclusion is explicitly only
`CountedResult Customs (Running ...) world.customs`; it is **not** a complete
counted loop boundary and is not installed in `f1_table` or `whileMin`.

Remaining obligations, without new assumptions of primitive or row results:

- Startup still needs the selected physical `Customs` predicate's actual
  zero witness. `f1_channelCounts_of` consumes that witness and the checked
  empty-head observation; it does not produce the physical zero.
- Ordinary `Running.stack`/`LoopAt`, entry and the shared payload/row
  producers still need one counted representation at their selected channel
  placement. The new unary setup producer consumes such counts; ordinary
  `CcallReady.of_loop` does not yet produce them. Counts through ordinary
  non-custom primitive summaries also remain to be carried by their frames.
- C_CALL returns must retain complete counts at the returned placement.
  Native `open_out_counts` already supplies opening counts, but the common
  counted callee post currently retains only the physical component. The
  out-list additionally needs its actual natural refcount increments and
  no-wrap proof; `OutListReturned.counted` and its frame outside refcounts
  do not establish those observations.
- The concrete `CustomMemCall` supplier remains named and open. Opening
  `OpenOutRuntimeAt.after` pins and out-list entry geometry/selected heap,
  matching named ledger and after-call runtime pins remain open. No runtime
  supplier was replaced with the desired row or primitive result.
- Named registration, general formatting, reset/libHeap and G2 remain open;
  `BarrierGrowthFull` stays with G2 and C4 round 2 still waits for F1. The
  `GoodF1` domain is unchanged.

Validation of this continuation passes:

- `scripts/lean-capped.sh lake build OCaml.Vm.Sim.CountedCcall1
  OCaml.Vm.Sim.F1Ccall OCaml.Vm.Sim.WhileMinTable`: **3,304 jobs**
  (`/tmp/a1-counted-loop-final-build.log`). This includes all five generated
  setup and suffix modules and the actual unary setup/readiness/call proofs.
- `scripts/lean-capped.sh lake env lean /tmp/a1-counted-loop-audit.lean`:
  **27 reports**, including all 17 new theorems and the ten ordinary
  compatibility projections. Every report uses only `propext`,
  `Classical.choice`, `Quot.sound` (`/tmp/a1-counted-loop-audit.log`, checked
  by `/tmp/a1-counted-loop-audit-check.txt`). The 17 new audits are registered
  in `OCaml/Audit.lean`; the full audit remains the lead gate.
- Hole, discipline and abstraction gates pass (C4 remains at 3), as do both
  changed generators' `--check`, the F1 generator's `--check`, and
  `git diff --check`.

Each build/audit used the capped wrapper with the inherited two-thread,
12 GB cgroup limit and `free -g` beforehand (available memory exceeded
25 GB). Intermediate proof corrections concerned footprint offsets and the
already-present stack reserve; final checks pass without increased budgets.
Only generators were edited for generated artifacts. No new trust primitive,
worker, virtual-memory limit, Git metadata or integration-queue write was
used. Checked edits remain uncommitted for lead review and integration.
This continuation remains **stuck at the ordinary counted loop invariant and
complete returned refcount evidence**, not at the unary setup frame.

**2026-10-27 counted-channel continuation: partial migration, not landed.**

`CustomMemCall.call` now returns `CustomMemCountedReturned`: the exact
`Customs f n → Customs d (n + 1)` is evidence from that execution's actual
`FnSummary` post. The invalid universal `Accounting.step` from the weak return
record is removed. `CustomAccounting` only supplies physical uniqueness,
caller-store framing and readiness from `ReadyOf`. `CustomFramed` and
`CustomCountStep` share framing/composition between consumers.

`OpenedOut.custom` retains the stronger return; `OpenedOut.counted` composes
the prefix, allocator and suffix physical transitions. The out-list walk
retains its count at each head, consumes one physical allocation per listed
record, frames the cons-cell allocation, and returns its whole batch charge
in `OutListReturned.counted`. `RestoreKept` names the final shared frame.
`ChannelCustomsAt` still distinguishes the pending refcount offset from the
physical custom count; allocation consumes that offset using the actual
counted post. `Ready` is never defined as a frame-stable refcount sum.

`open_call_ready` and `out_list_call_ready` use the successful reachable
successor's `Fits` bound. Both opening C_CALL adapters and the list adapter
consume `CountedCcallSetupPost.counts` and return `CountedResult` with the
physical successor count. `OpenOutRuntimeAt.budget` and the universal
out-list entry readiness were removed; `customBudget` is only the numeric
layout bound. `ccall_observed_return_on` exposes the shared pointwise return
adapter so the out-list retains its count on the same execution.
`ChannelRefsRepr.open`, `ChannelCustomsRepr.open`, and native `open_out_counts`
produce complete opened-channel counts using shared payload observations.
`f1_channelCounts_of` reads the actual empty startup list, conditional on the
physical-zero witness.

The ordinary invariant has **not** been migrated. `CountedVmReprAt` names the
intended stronger relation; ordinary `VmReprAt`/`WorldRepr`/`VmPayload` and
setup producers still omit it. A blanket `ChannelCountsAtCalls` implication
from every weak setup was inspected and removed; it would repeat the old
dead end. The generator now leaves ordinary open-in/open-out/out-list
`C_CALL1` summaries as explicit fields (five fields total in `F1CcallOpen`,
including named registration and integer formatting). `WhileMinOpen` likewise
retains the ordinary output-opening row. This is an intentional integration
blocker, not an extra `GoodF1` guard or a claim those suppliers are closed.

Remaining suppliers:

- a6-gc: concrete physical `Customs`, zero at startup, uniqueness/framing and
  readiness laws, and the actual counted allocator call (including named
  separation, heap/ABI effects and exact machine counter transition).
- a1-arms/a1-prims: carry `CountedVmReprAt` through every loop/payload/arm and
  actual C_CALL setup producer, then wire the counted summaries to those rows.
- a1-prims: the out-list's represented natural refcount increments and no-wrap
  proof; physical batch accounting alone does not supply these readbacks.
- a6-gc/a0-boot: open runtime `after` pins and the out-list's selected heap,
  record/named-ledger entry geometry and after-call runtime pins.
- Existing named registration/general formatting rows remain open;
  `BarrierGrowthFull` stays G2 and C4 round 2 waits for F1.

A downstream rebuild also exposed a preserved named-migration omission in
`LoopGeometry.of_above` (`PrimStringNotequalReturns`): its generic state
transport needed named-table equality. That equality is now explicit and
forwarded to `transport_ids`; its actual unchanged-world caller supplies it.

Validation passes:

- `scripts/lean-capped.sh lake build OCaml.Vm.Sim.OpenOutReturn
  OCaml.Vm.Sim.OutListAdapter OCaml.Vm.Sim.F1Ccall
  OCaml.Vm.Sim.WhileMinTable`: **3,684 jobs**
  (`/tmp/a1-counts-final-build.log`). This includes `F1Runtime`, the counted
  representation/readiness modules, native open/out-list chains and the
  named-table transport correction.
- `scripts/lean-capped.sh lake env lean /tmp/a1-channel-counts-audit.lean`:
  **52 reports**, all within `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/a1-channel-counts-audit.log`, checked by
  `/tmp/a1-channel-counts-audit-check.txt`). All focused reports are
  registered in `OCaml/Audit.lean`; its full run remains the lead gate.
- `check_holes.py`, `check_discipline.py`, `check_abstraction_gate.py`,
  `gen_f1_table.py --check`, and `git diff --check` pass. C4 remains at 3.

Builds/audit used the capped wrapper, two Lean threads and `free -g` before
each command (available memory remained above 25 GB). Earlier intermediate
build errors were proof/interface corrections, including the preserved
named-transport omission; the final build and audit pass. No virtual limit,
heartbeat increase, new trust primitive, subworker or generated-output edit
was used. The F1/whileMin tables were regenerated by their generator.

The checkpoint remains **stuck at ordinary counted invariant/setup producers
and the out-list refcount producer**. The checked interfaces do not close the
runtime suppliers. Git metadata and the integration queue remain untouched;
there is no new commit. The lead reviews, commits and lands.

**2026-10-27 physical named migration complete: checked worktree ready for lead review.**
The preserved `NamedRepr`, stronger `StackGeometry`, `LogWindows.named`,
`LoadedAt.named`, and arbitrary-byte/first-NUL lookup work remain intact.
No `GoodF1` restriction was added. The old alias witness now explicitly
uses `OldStackGeometry`; `StackGeometry.named_domain_disjoint` excludes it
from the strengthened invariant. The witness remains history, not a reason
to weaken that invariant.

`Gc.NamedLedger` links the physical named table to the **selected** live-block
list in `LibHeapAt H cap chs c`. Its snapshot includes `NamedOwned H`, and
`NamedRepr.foot_eq` matches that snapshot to the consumer's representation
using physical chain addresses and terminated-key lengths. It does not infer
ownership for arbitrary `HeapReady H`, or put dynamic nodes in `f1Covered`.
`namedBlocked` separates nodes from fixed runtime allocations, channel
records, and allocated remembered-set storage. Startup, safe-window and
record frames, insertion, linking, and growth preserve that selected witness.
`NamedOwned.append` and `.values` supply the new-node and replacement
ownership constructors using actual requested sizes, without fixed name
length or registration-count limits.

The channel-opening consumer uses that ledger for malloc freshness and
preservation of named bytes. `CallerApart.named` states the required custom
state separation inside the existing `CustomMemCall` contract. Its concrete
machine supplier remains an explicit obligation, alongside the rest of that
contract; the consumer no longer tries to derive it from `.free` or from
fixed extent coverage. The remembered-set separation interface consumes the
already represented named table. Console and allocation consumers retain
named bytes through the shared payload, geometry and log frames. The
channel-list runtime entry exports `NamedLedger H [] c` alongside
`HeapReady H cap c` for the walk's same `H`; `out_list_entry` derives named
read safety from that matching witness and the represented table, and
`PayloadMisses.named` carries it through the predicate frame. This checked
conditional producer does not discharge the concrete `OutListRuntime` machine
supplier. Startup's bucket proof reads the checked log's final view, including
its zero stores.

Focused producer/consumer validation passes with 2,442 jobs:
`scripts/lean-capped.sh lake build OCaml.Vm.Gc.F1Grow
OCaml.Vm.Sim.OpenOutReturn OCaml.Vm.Gc.NamedOwnership`
(`/tmp/a1-named-consumers-next.log`). The additional `Sim.F1Growth` and
`Sim.PrimMlOutput` focused consumer build passes with 2,556 jobs
(`/tmp/a1-named-growth.log`). The channel-list and channel-opening return
check passes with 2,409 jobs (`/tmp/a1-named-outlist.log`). The complete
`scripts/lean-capped.sh lake build OCaml` passes with **4,151 jobs**
(`/tmp/a1-named-complete.log`).

The focused audit, `scripts/lean-capped.sh lake env lean
/tmp/a1-named-physical-audit.lean`, passes with **71 reports**, all using only
`propext`, `Classical.choice`, and `Quot.sound`
(`/tmp/a1-named-physical-audit.log`, checked by
`/tmp/a1-named-physical-audit-check.txt`). Every focused report is registered
in `OCaml/Audit.lean`; its full execution remains the lead gate.

**Separate primitive-machine obligations:** this migration does not discharge
`F1CcallOpen.ml_open_descriptor_out_c_call1`,
`.ml_open_descriptor_in_c_call1`, `.ml_out_channels_list_c_call1`,
`.register_named_value_c_call2`, or `.format_int_c_call2`. The existing
`register_named_value_run` is a native summary; the represented C_CALL adapter
and its runtime/resource post remain separate work. `CustomMemCall` remains
a named premise, including the physical named/custom separation supplier.
`BarrierGrowthFull` remains with G2; C4 discovery round 2 waits for F1.

Builds use the inherited 12 GB cgroup and two Lean threads, with `free -g`
before each command and the per-worktree lock. Failed builds are terminated
before retrying. No virtual-address limit, heartbeat increase, hole, or
new trust primitive was introduced. Hole, discipline and abstraction checks
and `git diff --check` pass. No generated Lean source was edited. The preserved
checkpoint is `ca56c230`. Git metadata and the landing queue remain untouched;
the lead reviews, commits, and lands through `scripts/integrate.sh`.

**Console output (in progress, shared by all channel primitives):**
* `ConsoleWrite.write_console` (`Console/Write.lean`): newlib `_write(fd, buf, n)` on a
  console descriptor prints the buffer by one HTIF putchar per byte (`putchar_step`,
  ported `stepObs_tohost_putchar`; `console_loop` by `loopFromBody`) and returns `n`;
  output = old ++ `bytesToString bytes`; premises `WriteLayout` (96-byte frame) and
  `ConsoleFd` (fs_ready, fd < 32, descriptor kind > 1 and ≠ 4). Generated blocks:
  `gen_fn.py --ocaml-write`.
* `ConsoleWrite.write_fd` (`Console/WriteFd.lean`): `caml_write_fd(fd, flags, buf, n)` on
  a console descriptor returns `n` with the bytes appended to the output and s0–s7
  restored; it writes only `[sp-192, sp)`, `errno` and the reentrancy errno word.
  Premises: `WriteFdLayout`, `ConsoleFd`, the default enter/leave hooks
  (`0x8000d2a4`/`0x8000d2a8`), `_impure_ptr = rp`, `NoPendingSignals`, `n < 2^31`.
  Parts: `enter_blocking`, `write_call` (write → `_write_r` → `write_console`),
  `leave_blocking` (`scan_loop` over the 32 pending-signal slots by `loopFromBody`);
  `indirect_registers_summary` (`IndirectCall.lean`) for the hook's `jalr`.
* `ConsoleWrite.flush_partial` (`Console/Flush.lean`): a console channel's whole buffer
  through one `caml_write_fd` (`flush_written`), or nothing for an empty buffer
  (`flush_empty`); `offset += n`, `curr := buff`, result 1. Shared prologue `flush_head`
  and epilogue `flush_epi`. Memory premises `FlushMem`, transferable over `FlushReads`.
* `ConsoleWrite.ml_flush` (`Console/MlFlush.lean`): `caml_ml_flush(vchannel)` with null
  channel-mutex hooks: local root registered and restored, `flush_partial` once, `Val_unit`.
  Post `MlFlushPost`: output ++ bytes, curr/offset, s0–s11 and sp preserved, memory framed
  outside [sp-384, sp), the errno words, the two channel words and `local_roots`.
  Split by phase (`ml_flush_pro/_enter/_written/_flushed`) to stay within the elaboration
  budget; separation facts in `MlFlushLayout.sep`. The prologue (`ml_flush_pro_gen`,
  input `MlFlushEntry`) and epilogue (`ml_flush_tail`) are shared with the closed channel
  (`fd == -1`, `ml_flush_closed`: straight to the epilogue, generated `closed_fast`).
* Generated block wrappers: `scripts/syi/ocaml_block_wrappers.py` emits `<block>_fast`
  from an access spec (windows, logs over loads, `@k` addresses, branch conditions,
  reloaded ra). Loads after the block's own stores use `BlockPins.accessPlan_of_pure`
  (each load misses only the stores before it). Used for the flush path; the earlier
  hand wrappers (FdWrite/Console/ExitPath `Effects.lean`) are to be migrated, after
  which a discipline rule should forbid hand `registers_of_blocks` wrappers.
* Rules (foreman, 2026-10-06): no new `decide +kernel` over the whileMin run (extend
  `St.shapeOk`); no per-program premises in the headline. Primitive premises are
  native-layout/runtime facts at the call site; the flush adapter's "channel fd is an OS
  output stream" premise belongs to the running-platform invariant.
* Debt: the saved-frame readbacks (`back`/`apart` tuples in write_fd, flush_partial,
  ml_flush, output_char) repeat per primitive; factor a frame-log readback lemma (entries
  `(base + k, 8, v)` plus one extra word) before caml_ml_output_bytes.
* Lean notes: `omega` hits max recursion on `s - 112 - 272` with disjunctions (normalize
  with `Nat.sub_sub`), and evaluates `def` constants like `errnoGlobal.toNat` in
  hypotheses (rewrite them to numerals first).
* `ConsoleWrite.oc_room` / `oc_full` (`Console/OutputChar.lean`): `caml_ml_output_char`
  on a buffered console channel with null mutex hooks; room in the buffer (byte at
  `curr`, `curr + 1`) or full (one `flush_partial` of the 65536-byte buffer, then the
  byte at `buff`). Phases `oc_pro` / `oc_tail` / `oc_full_enter` / `oc_full_flushed`.
* Repr: WorldRepr carries the object-ID counter (`WorldRepr.ooId`), ChanAt the buffer end,
  a clear unbuffered flag, and (last conjunct) `cursor ≤ ioBufferSize ∧ buffer.length ≤
  ioBufferSize ∧ a % 8 = 0` (`ChanAt.fields`/`.cursorLe`/`.bufferLe`/`.aligned`); PayloadOutside/PayloadCoreOutside an `ooId` window.
  `VmPayload.frame_chan` (`ChannelFrame.lean`): payload across a footprint that rewrites one
  channel record, which then represents the channel's new state.
* Console statics: `ConsoleRuntime` (`Console/Runtime.lean`): fds 1/2 consoles, default
  blocking hooks, `_impure_ptr`, no pending signals/actions, null channel-mutex hooks; a6-gc
  pins it for F1 (`f1_consoleRuntime`). Console streams: bprime's `GoodF1.consoles`
  (`OCaml.ConsoleChannels`, out channels with fd ≠ -1). BcSem guards (a2-sem, landed):
  `offsetFits` (offset + n < 2^63) and `isOut` on flushChan/putChar/putBlock.
* Console C_CALL adapters. Shared pieces in `Sim/ConsoleCall.lean`: `consoleWindows sp a` /
  `consoleLog sp a` (native stack, errno words, a channel record's offset/curr words and
  buffer: the one footprint of every console primitive) and the named premise
  `ConsoleStable L` over a getD frame (`FrameOnD`; a6-gc: `f1_console_stable`, FIXED
  `consoleStable`), `ChannelArg`/`channel_arg`, `console_geometry` (`ConsoleGeometry` from
  `LoopGeometry` + `NativeValid`; layouts in `Console/Geometry.lean`, addresses checked
  against the ELF by `console_symbols`), `ChanAt.update` (a record after an offset/curr/buffer
  update), `ConsoleRet` + `framed_of_ret` (any console return to `FramedPrimitivePost`).
  `caml_ml_flush` (`Sim/PrimMlFlush.lean`): `flush_framed` (open console channel),
  `flush_closed_framed` (fd = -1). `caml_ml_output_char` (`Sim/PrimMlOutputChar.lean`):
  `output_char_semantics`/`PutCharCase`, `char_byte`, `oc_input` (from a full-extent
  `ConsoleGeometry`), `oc_room_framed`, `oc_full_framed`. The payload/binding apartness of
  the footprint are premises of the framed theorems.
  Waiting on a1-arms (`CcallSetupPost.calleeSaved`; channel-record apartness at full extent;
  transport with a weaker `chans` premise) and a6-gc (`f1_console_stable`) for
  `prim_caml_ml_flush_returns` / `prim_caml_ml_output_char_returns`.
* `caml_ml_output_bytes` (machine, `Console/OutputBytes.lean`; model loop,
  `Sim/PrimMlOutput.lean`). Phases: `ob_pro`, `ob_none` (len ≤ 0), `ob_go`, the chunk
  blocks `ob_small` (no INT_MAX clip below 2^31), `ob_test` (room/full), `ob_room`
  (memmove, `curr += n`, exit), `ob_fill` (memmove `free` bytes), `ob_flushed`
  (`curr := end`, `caml_flush_partial`), `ob_next`, `ob_restore`, `ob_exit`; memmove calls
  through `ob_move` (memmove_leaf + `MoveRet`). Loop: `ObLoop` (machine state + model
  channel/world, `ChanAt`, console), `ob_iter_room` / `ob_iter_full` against
  `putBlock_room` / `putBlock_full`, measure `obMeasure` (2·rem + [buffer full]),
  `ob_loop` by `loopFromBody`; `ob_finish` and `ob_bytes` (whole function against
  `putBlock`, posts `ObDone`). Model lemmas in `Console/World.lean`: `putBlock_full_fits`,
  `putBlock_fuel`, `putBlock_nil`, `putBlock_shape` (only the channel and the OS change).
  `caml_ml_output` is the generated tail `j` (`Flush/MlOutput.lean`; `tailj` wrappers in
  `ocaml_block_wrappers.py`). Remaining: the C_CALL4 framed theorem (string argument
  from `ObjAt` + StackGeometry's heapLow/heapArena/heapChannels/domainHeap).
* `GprsKept` (`Primitives/GprsKept.lean`: register presence and gp, `of_pins`/`of_gprs`/
  `gprPresent`) is carried by every console post (loop, write, write_call, blocking hooks,
  write_fd, flush_partial, ml_flush, output_char, output_bytes) and by
  `FramedPrimitivePost.gprs`; `LibraryReady.of_kept` re-derives memmove readiness after
  calls. The console native window is `sp - 512` (output_bytes reaches 448 deep).
  `console_geometry_full` gives the channel record at full extent (65536).
* **Console `PrimReturnsAt`** (`Sim/PrimConsoleReturns.lean`): `prim_caml_ml_flush_returns`
  (open and closed channels) and `prim_caml_ml_output_char_returns` (room/full) proved for
  every program from `ConsoleStable L`, the console statics from `runtimeOk` and
  `ConsoleChannels P` (FIXED `consoleStable`/`consoleRt`/`consoles` in `gen_f1_table.py`, with
  `FIXED_IMPORTS`). Shared glue in `Sim/ConsoleCall.lean`: `console_site` (invocation, channel
  argument, `console_outside`/`console_bindings`: the footprint misses the payload and the
  bindings), `console_callee_summary` (framed summary to `CcallReturn` via
  `ccall_framed_summary`; `console_loopGeometry` transports the geometry).
  `prim_caml_ml_output_returns` (C_CALL4): `output_framed` (empty writes on any channel via
  `ob_empty`; console facts from `putBlock_open` + `ConsoleChannels`), `LibraryReady` from
  `CcallSetupPost.libraryReady` with the named premise `CcallEntryGprs L` (OPEN_PARAMS
  `ccall_entry_gprs` in `gen_f1_table.py`; a1-arms discharges it with `LoopRegisters.gprs`).
* **Read-only `PrimReturnsAt` at every C_CALL opcode** (for `CcallReturns.of_primsF1`):
  `prim_constant_returns` (`LeafPost.toRegisterPost`, `const_shape`) for the nine
  `caml_sys_const_*`; `prim_length_returns` for string/bytes length; `prim_caml_int_compare_returns`.
  `prim_caml_ml_output_bytes_returns` via `prim_output_returns_at` (`ObEnter`: `output_enter` is
  the tail `j`, `output_bytes_enter` the identity). Gaps for the rest of `primsF1`: see PHASES.
* **String padding in `ObjAt`**: `.bytes`/`.partialBytes` now record the zero bytes between the
  string and the pad byte (`caml_alloc_string` zeroes the last word). Producers: `StringShell.object`,
  `gen_boot_heap.py` (asserts and proves them from the capture), `Reloc.bytePayload`. Consumers:
  `paddedString_of_objAt`, `prim_caml_string_equal_returns` (contracts take `strOf?`, so initialized
  `.partialBytes` too).
* `prim_caml_string_notequal_returns`: the saved-`ra` store lies just below the native sp (above
  the arena); `ccall_writing_summary_below` (CcallWriting.lean: `NativePlaced.frame_below`, callee
  post and C-call registers given directly since the wrapper writes and restores sp),
  `LoopGeometry.of_above`, premise `nativeStable` (F1: `f1_native_stable`, FIXED in gen_f1_table.py).
* whileMin `PrimReturnsAt` summaries (picked up by `scripts/gen_f1_table.py`; regenerate
  WhileMinTable.lean in the same batch): `prim_caml_ml_string_length_returns` and
  `prim_caml_fresh_oo_id_returns` (`f1_counterStable` from a6-gc's `f1_ignoredStatic`) done.
* Split agreed with bprime (2026-10-06, foreman): bprime takes `caml_format_int` (C_CALL2)
  and `caml_ml_open_descriptor_out` (C_CALL1); a1-prims keeps `caml_ml_flush` (C_CALL1),
  `caml_ml_output_char` (C_CALL2) and `caml_ml_output` (C_CALL4), the flush_partial →
  caml_write_fd → _write chain.
  On 2026-10-12, bprime also took `caml_ml_open_descriptor_in`: the two primitives differ
  only by `max := NULL`, so both are instances of bprime's channel-opening path
  (`Primitives/Channel/`). `caml_register_named_value` waits on a0-boot's
  `caml_named_value`.
* Split with a1-arms (2026-10-19, foreman: a1-arms joins the C_CALL returns). a1-prims keeps
  `caml_sys_executable_name`, `caml_sys_get_argv` and `caml_register_named_value`. a1-arms takes
  `caml_sys_exit` (vacuous: `prim_caml_sys_exit_returns`, `Sim/PrimSysExitReturns.lean`),
  `caml_ml_out_channels_list`, and the per-arity assembly (`CcallReturns.of_primsF1` into
  `F1Premises` via `gen_f1_table.py`). For out_channels_list, a1-arms writes:
  * the site-generic `CustomMemCall` (`Gc/CustomMem.lean`; bprime's and a1-arms' call sites
    are instances; a6-gc refines `Ready` with the extra-heap-resources bound);
  * `ChanFields.managed` (flag bit 4);
  * the ordered `channelsListed`;
  * the `allocPlaces` entry.
  bprime keeps `open_descriptor_out/in` and `format_int`.
* Next: finish the flush adapter (`ccall_framed_summary`), then output_char, then
  `output_bytes` (a2-sem's `memmove_summary`, `Primitives/Memmove.lean`) and `output`.
* Exit path weakened to `ExitOk` (registers read: ra, sp, a0, s0–s10) for STOP;
  `EffectPost.htifIdle` (`HtifFrame.lean`) for a1-arms' `LoopRegisters.htifIdle`.

* Allocating primitives at C_CALL (`Sim/CcallAllocation.lean`): `ccall_allocation_entry` takes a
  primitive's represented contract for one object reserved below `young_ptr`, and builds
  `AllocationInput` (`AllocLogOk.of_block`), the runtime frame (`AllocFrame`, F1: `f1_allocFrame`)
  and the C_CALL return (`ccall_logged_summary`: the geometry after the call uses the exact log,
  `LoopGeometry.alloc_log`). Inputs: the entry placement and the post-call budget, both from
  a1-arms. CcallCallee/PrimReturnsAt change (928bff62). `prim_caml_int64_float_of_bits_returns` (every C_CALL, premise `AllocFrame L`) from `int64_float_entry`
  (`Sim/PrimInt64FloatReturns.lean`): `FastMemory` from the reserved block.
* `prim_caml_sys_argv_returns` (`Sim/PrimSysArgvReturns.lean`): read-only, from a1-arms'
  `VmPayload.argv` (861f1ce1); result word `(valWord pl world.argv).getD 0`.
* String-allocator infrastructure (for `get_config`, `get_argv`, `executable_name`):
  `PrimAllocFrame L` (`Sim/PrimAllocFrame.lean`; F1: `f1_primAllocFrame` over a6-gc's
  `f1_allocation`): stores in the free nursery, above the arena, or in the domain's
  `young_ptr`/`local_roots` keep the runtime. `LoopGeometry.reserve` (`Sim/AllocChain.lean`):
  chained reservations on virtual configs. `ccall_observed_summary` + `framed_of_library`
  (`CcallAllocation.lean`): library-style posts at the C_CALL return. `StringAllocEntry`
  (entry scalars), `getConfigLog_in` (the get_config log in four windows), `StringAllocReturn`.
* `prim_caml_sys_get_config_returns` (`Sim/PrimGetConfigReturns.lean`): `config_input` discharges the
  generated contract's `GetConfigInput` at the callee entry from `StringAllocEntry` (`ConfigInput.lean`:
  `prepare_access`, `config_site` + `copy_memory_at` = `CopyMemory`, `config_small`, the
  finish layout); `get_config_entry` combines the contract with `PrimAllocFrame` (final `young_ptr`
  `Y - 48`, `getConfig_young`), `LoopGeometry.reserve2` and `ccall_observed_summary`. `get_argv` and
  `executable_name` reuse the copy-stage lemmas.
* `copy_memory_at` (`Sim/CopyStringInput.lean`): `caml_copy_string`'s `CopyMemory` from a `CopySite`
  (native sp, domain, nursery, source C string); `get_config` instantiates it (`config_site`).
  BcSem's exe name is the constant `progExeName` ("/prog", a2-sem 7606766c); the contracts and the
  string-wrapper/argv generators use it.
* `allocPlaces` covers `caml_ml_open_descriptor_out/in` (bprime): the channel's custom block at
  `young − 16` (`caml_alloc_custom_mem`, wosize 2).
* `prim_caml_sys_executable_name_returns` (`Sim/PrimExecutableNameReturns.lean`): the primitive
  tail-calls `caml_copy_string`, so `copy_memory_at` applies at the callee entry (`exe_site`: sp `N`,
  source `Gc.exeNameAddr`, 5 bytes, span 8). Premise `ExeNameAt L` (pointer, `"/prog\0"`, apart from the
  domain record; F1: `f1_exeNameAt` from `F1Pins`, FIXED in `gen_f1_table.py`). `copyMemory_eq`: the
  contract's memory is `completeLog`'s effect; the log lies in `allocWindows N D Y 16` (the four-window
  hub, now over any nursery block size); young pointer `Y - 16` (`exe_young`); geometry
  `LoopGeometry.reserve1`.
* `prim_caml_sys_get_argv_returns` (`Sim/PrimGetArgvReturns.lean`): the argv instance of
  `get_config`. `ArgvLogWindows.lean` puts `getArgvLog` in `allocWindows N D Y 40` (16-byte name block
  plus the 24-byte pair; young pointer `Y - 40`, `getArgv_young`); `ArgvInput.lean` gives the stage
  inputs (`argv_prepare_access` with the third load `caml_exe_name`, `argv_small`, `argv_finish_layout`,
  `argv_site` = `CopySite` on the executable name after the prepare stores). Premises `PrimAllocFrame L`,
  `ExeNameAt L`; the pair's second field is `main_argv` (`VmPayload.argv`). `ConfigNumbers` is now
  `AllocNumbers … 48`. The config/argv stage files are two instances of one tuple shape; a third
  string-then-block primitive must factor them first (rule 3).

**Next (remaining, path-specific callees):**
* `caml_register_named_value`: `register_named_value_run` (`Named/RegisterTail.lean`) proves the
  whole function from `RegisterTable` to `Registered`. Pieces:
  * `NamedTableUpdate.lean` (over a2-sem's `Agree`/`TableFoot` transport): `TableShape.update`/`insert` (the found
    node's new value, an absent key's fresh node at its bucket's head) and `TableBlocks` (keys distinct per
    bucket, nodes apart, in live malloc blocks).
  * `RegisterTail.lean`: `epilogue`, `found_tail`, `miss_allocate` (`strlen`, checked `caml_stat_alloc`),
    `miss_link` (`memcpy`, link stores, root registration).
  * The global-root callees are the named contract `RootCalls`.
  * a0-boot's `strlen_ready`, `memcpy_window`/`memcpy_fresh`, `of_same_memory` and `of_window_frame` now
    take any `LibraryLive` set (`…L` structures with startup abbrevs); `MemcpyFreshDoneL` gained `output`.
  * Open before `PrimReturnsAt` (user decision 2026-10-20: machine run first, invariants recorded):
    `NamedTableAt` in the loop invariant, node and skiplist room in `LibHeapAt`, RAM presence at the C_CALL
    entry (boot density plus a2-sem's `memPersist`), a `RootCalls` instance (a6-gc's `Skiplist.Ops` is the
    skiplist side). `GprsPersist_Statement` is proved (`gprsPersist`). See PHASES.md.
* The two global-root callees as machine runs over a6-gc's `Skiplist.Ops` and `PageTableLookup`
  (blocks generated by `scripts/syi/ocaml_named.py`, namespaces `RegisterRoot`, `ModifyRoot`):
  * `register_root_run` (`RegisterRootRun.lean`): `RootInput` → `RootFiled` (immediate: return; young:
    tail call into the young list; otherwise the page table, `In_heap` into the old list).
  * `modify_root_run` (`ModifyRootPaths.lean`): `ModifyInput` → `RootModified` (`*r = v`; `RootAt` places
    `r` for `v`). Between the prologue and the store the run keeps `Acting` (`ModifyRootRun.lean`); a list
    call steps it (`Acting.step_young`/`step_old` over `OpEntry.insert`/`remove`).
  * `ModifyRootClassify.lean`: the four value classifications are one `classify` (exits named by `Lands`);
    the old-`v` and other-`v` paths share the `WBlocks` bundle (`oBlocks`, `xBlocks`, one `wClassify`).
  * `ModifyRootFinish.lean`: the three store blocks are one `StoreBlock`; `Acting.finish` ends every path.
  * `RootsUpdate.lean`: the roots' algebra across a list call (`replace_*`, `insert_*`, `remove_*`,
    `GlobalRoots.keep`).
  * `RootCallsG` (below) is proved from these two runs (`rootCallsG`, `GenRoots.lean`), and
    `register_named_value_run` is ported onto it: `found_tail` (`RootCallsG.modify` on a registered slot),
    `miss_link` (`RootsAt.keep` across the allocation and link stores, `Fresh` for the node's value word,
    `RootCallsG.register`), post `NamedRootsAt`. Posts carry `link` and the HTIF register; readiness after a
    roots call is `RootsReturn.ready`. `TableBlocks.live` is byte-wise (outside newlib's footprint).

**`RootCallsG` (replaces `RootCalls`; `OCaml/Vm/Primitives/Named/GenRoots.lean`; landed shape).** `RootCalls`
keeps bytes outside static statics `G`, but the skiplist cells live in the heap, and both calls need the
roots' state at entry. The new contract carries a roots invariant over memory:

* `RootsState`: `rs ys os` (the three lists' keys), `cls` (page-table classes), `D start stop`
  (`Caml_state`, `young_start`, `young_end`), `slots` (registered generational slots).
* `RootsAt Shape foot Table tfoot H S m` (named fields): `env : EnvAt` (`table`, `young`, `startBelow`/
  `stopBelow`, and `tableOff`/`stateOff`: the page table's footprint `tfoot m` and the
  `Caml_state` words are `Off` — off `ListsFoot m`, `vsaFoot H` and `random_seed` — and outside the slots);
  `roots : GlobalRoots Shape foot m rs ys os`; `placed : ∀ r ∈ slots, RootAt start stop cls (*r) r ys os`;
  `slotLow`/`slotHigh`/`slotAligned`/`slotOff`/`slotsApart`; `listed : ys, os ⊆ slots`; `notGlobal`;
  `globalOff` (`caml_global_roots`' keys are allocated words off the lists).
* `Fresh … r`: a slot fit to register (new, aligned in the arena, `Off`, apart from the slots, the page table
  and the state words). `Carry H H' own m m'`: what a call guarantees about memory; `EnvAt.carry`,
  `RootsAt.register`, `RootsAt.modify` move the invariant across it.
* a6-gc's `PageTableFrame Table tfoot`: the page table keeps its classes and footprint under stores off
  `tfoot` (`PageTableLookup.frame` asks agreement on all of the arena, which a skiplist insertion breaks).
* The list footprint is `ListsFoot Shape foot m` (memory-dependent); posts keep every byte outside it, newlib's
  footprint, the stack window, `random_seed` (and the slot for `modify`), and give `RootsAt` again on a
  successor state (`slots` gains `r` for `register`) with `vsaFoot H'` and `ListsFoot d` within the old ones.
* Supplied by a0-boot at the whileMin cut (agreed 2026-10-20; later startup steps change `cls`, `H` and
  `Caml_state`): `RootsAt` with empty lists and slots (`Shape m sk []` for the
  three headers), `table`/`tfoot` after the page table's set-up, `young` (`Caml_state`, the minor heap's
  bounds), the apartness fields. By a6-gc: `Skiplist.Ops`, `PageTableLookup`, `TableFrame`. By a1-prims:
  `RootCallsG` from `register_root_run`/`modify_root_run`.
* channels: `open_descriptor_in/out` → `caml_open_descriptor_in` (`caml_stat_alloc`,
  `lseek`) + `caml_alloc_custom_mem`; `output_bytes`/`output_char` (buffer `memmove`,
  `caml_flush_partial` when full); `flush` → `caml_flush_partial` → `caml_write_fd` →
  `write` → `_write` (209-instruction HTIF/FS emulator; check a0-boot's startup rows
  for an existing `_write` summary first); `output` tail-jumps to `output_bytes`;
  `out_channels_list` walks `caml_all_opened_channels`.
* `caml_format_int`: `parse_format` + `caml_alloc_sprintf` (newlib vsnprintf; check
  the A0 `LibraryFormat` specs).

**2026-10-05 (Claude session, taking over from Codex). 21/30 summaries proved.**

* `caml_sys_exit`: `ExitPath.caml_sys_exit_halts` (`OCaml/Vm/Primitives/ExitPath/Primitive.lean`):
  from the represented call site plus the named `ExitRuntime` (VsaOk, native stack
  window `ExitLayout`, the four runtime globals zero), the machine `Halts` with
  `primF1Impl`'s status and console. Machine run `exit_halts` (`Machine.lean`) over
  generated blocks (`gen_fn.py --ocaml-exit`, new stage-a5 check) and the HTIF step
  `store_halts` (ported `Vsa/Sim/TermEntry.lean`). New Layout symbols: caml_verb_gc,
  __atexit, __atexit_recursive_mutex, __stdio_exit_handler.
  `ExitPath.do_exit_halts` (`Machine.lean`) is the shared `caml_do_exit(code)` run from
  its own entry (`DoExitInput`: status in a0, any aligned ra, 208-byte stack window,
  the four globals), with `exitStatus_zero` for STOP: a1-arms/bprime can discharge
  `StopDoExitSummary` from it; `caml_sys_exit_halts` serves the C_CALL
  `PrimitiveExitSummary`.
  libc `exit` from its own entry: `ExitPath.libc_exit_run`/`libc_exit_halts` (`LibcExitInput`, 112-byte window; a null `__stdio_exit_handler`), factored out by a2-sem into `exit_procs_run` + `exit_tail_run`; `do_exit_run` is its prefix spliced onto it. The installed-handler branch (after `__sinit`) is `libc_exit_handler_halts` (`LibcExitHandler.lean`, a2-sem).

Done this session:
* `caml_sys_get_argv`: machine run `ArgvTuple.argv_finish_stage`
  (`ArgvTupleFinished.lean`) over the copy/allocation stages (landed `88ba657`);
  `finish_access` discharges the generated finishing block's 13 scalar accesses
  from `FinishLayout` windows, and every loaded value (string root, pair,
  `main_argv`, `Caml_state`, saved ra/s0/s1/s2) is read back from the exact
  write logs (`saved_readback`, `Gc.word_writeLog_at`). Represented contract
  `get_argv_contract` (`GetArgvContract.lean`): payload/bindings framed over
  `getArgvLog`, then two `VmPayload.allocate` steps (name bytes, then the pair
  `[name, World.argv]`). Headline `caml_sys_get_argv_primitive` is generated.
* `caml_sys_get_config`: block certificates from the shared generator backend
  (`ocaml_argv_tuple.emit_tuple_blocks`, argv output byte-identical); stages
  `ConfigTuple{Fast,Copied,Allocated,Finished}.lean`, contract
  `get_config_contract` (`"Unix"` bytes, then `[ostype, 64, false]`), generated
  headline `caml_sys_get_config_primitive`.

Duplication note (law 3): argv and config are two instances of "native frame:
copy a C string, allocate a small block, fill fields". The config stages were
adapted from argv's. A third instance must first factor the stage composition
(prefix block + JAL + callee summary; predicted-memory `finishLoads` with
`lpins8_of_view`; saved-register readback) rather than copy it.

Open, next: `caml_sys_exit` (tail into `caml_do_exit`: halt behaviour), the
channel family (`open_descriptor_in/out` via malloc and custom alloc,
`out_channels_list`, `flush`, `output_char`, `output`=tail jump to
`output_bytes`), `caml_format_int` (`parse_format` + `caml_alloc_sprintf`),
`caml_register_named_value`.

Executable-name allocation now passes its focused build: 18/30 summaries
proved, with full copy-string/memcpy execution and represented fresh bytes.
The complete 2,023-target build and axiom audit pass (standard axioms only);
landed at `9ba7eef` after the complete integration gate. Twelve remain.

Started `lane/a1-prims` from origin/main (`bf5d5df`) in the reused a0-lib
worktree. Read the lane brief, COMMON.md, CLAUDE.md, PLAN.md and PHASES.md;
ran the abstraction inventory. The landed `PlatformOk`/`Running` contract is
in scope. Nine constant primitive summaries are proved and landed at `c4b42e0`;
the first milestone passed the complete integration gate. Signed integer
comparison is now proved (10/30 total), with its shared read-only register
frame and tagged-order lemmas. The complete axiom audit passes (1,083 targets,
standard axioms only) and the milestone is landed at `d4ebfc4`.
Argv and both string/bytes length summaries now build against the migrated ELF
(13/30 proved). Their shared heap/access-window bridge and code certificates
compile within the default budgets. The complete build and axiom audit pass
(1,119 targets; only the permitted standard axioms). The complete integration
gate passed and the accessor milestone is landed at `029d516`.

`caml_fresh_oo_id` is proved (14/30 total), including the updated counter
and VM payload frame. Its generated module compiles in 1.7 seconds; the complete
regression build and axiom audit pass (1,273 targets, standard axioms only).
The complete integration gate passed and the milestone landed at `54ce77c`
(39,560 pinned bytes, zero mismatches).

`caml_string_equal_primitive` now compiles (15/30 proved), including alias,
unequal-size and finite word-loop paths. The full build and axiom audit pass
(1,343 targets, permitted standard axioms only). The complete integration
gate passed after rebasing concurrent boot/arm work, and the milestone landed
at `24ef4c7`.

`caml_string_notequal_primitive` is proved (16/30), with a generated native
stack save/JAL/restore wrapper around the equality summary. The complete
machine call splice and represented contract pass their focused build; the
full regression and axiom audit pass (1,891 targets; standard axioms only).
The complete integration gate passed and the milestone landed at `5aec151`. The native sp is restored, and the saved
return-address write is framed from the represented heap/world and primitive
bindings using explicit static separation. The whole wrapper uses the default
proof budgets.

## Inventory and next work

`results/primitives-f1.json`, regenerated by `scripts/gen_primitive_census.py`,
records all 30 `primsF1` entries, instruction counts, and external/indirect
transfers from the pinned ELF. `gen_layout.py` now emits their symbol addresses
and the three primitive globals `main_argv`, `caml_exe_name`, and `oo_last_id`.

Nine system constants share a register-only leaf shape (two instructions,
three for max_wosize). They now use the `gen_fn.py --ocaml-constants` backend,
which calls the original CFG extractor and folds the existing segment kernel.
Integer comparison uses `--ocaml-compare`; argv and length accessors use
`--ocaml-argv`/`--ocaml-lengths`. The six-instruction `--ocaml-counter`
family reads and updates `Layout.sym_oo_last_id` with a shared memory-region
frame and explicit link to `World.ooId`. Next are the allocating/channel primitives and process exit. Calls and tail calls
will use `FnSummary.callSplice` / `tailJump` and the landed A0 library specs.

The unused legacy generator backend still has WHILE-specific path defaults
and only folds a counted byte-output loop. The new ELF backend emits neither
budget overrides nor unavailable import assumptions.

The current `WorldRepr` constrains console/channels but not argv's global,
executable-name storage, the object-ID counter, or named-value table contents.
Those primitive-specific input invariants must be made explicit and preserved.
`VmReprAt.atHead` is a dispatch-loop predicate, so a primitive-call boundary
must separate its data representation from PC and argument/result registers.
The arbitrary `Layout.runtimeOk` also needs an explicit frame-stability
interface before preservation can follow from a callee's register/memory frame.

The string equality ELF compares complete words, including padding. `ObjAt`
currently records payload bytes and the final padding-count byte, but not
intermediate zero padding. The string family therefore needs an explicit
padding invariant supplied by `caml_alloc_string` (`runtime/alloc.c:93` zeros
the final word before writing its count byte); the current representation
alone does not justify whole-word equality.

## Primitive theorem table

Each theorem is in `OCaml/Vm/Primitives/<module>.lean` and generated by
`gen_fn.py` with `--ocaml-constants`, `--ocaml-compare`, `--ocaml-argv`,
`--ocaml-lengths`, `--ocaml-counter`, `--ocaml-string-scan`, or `--ocaml-string-wrapper`. The `_primitive` theorem connects the C entry
and return to `primF1Impl`, carries the represented VM payload/result, and
preserves the platform and saved caller registers. Read-only callers supply
`MemoryStable runtimeOk`; `runtime_memory_stable` proves this for the current
`RuntimeOk` from the free-list predicate's memory-frame law. The counter
uses `WindowStable` plus payload/table separation. String equality also
requires the named `PaddedString` allocator invariant.

| Primitive | Theorem | File:line |
|---|---|---|
| `caml_sys_const_naked_pointers_checked` | `caml_sys_const_naked_pointers_checked_primitive` | `CamlSysConstNakedPointersChecked.lean:95` |
| `caml_sys_const_big_endian` | `caml_sys_const_big_endian_primitive` | `CamlSysConstBigEndian.lean:95` |
| `caml_sys_const_word_size` | `caml_sys_const_word_size_primitive` | `CamlSysConstWordSize.lean:95` |
| `caml_sys_const_int_size` | `caml_sys_const_int_size_primitive` | `CamlSysConstIntSize.lean:95` |
| `caml_sys_const_max_wosize` | `caml_sys_const_max_wosize_primitive` | `CamlSysConstMaxWosize.lean:113` |
| `caml_sys_const_ostype_unix` | `caml_sys_const_ostype_unix_primitive` | `CamlSysConstOstypeUnix.lean:95` |
| `caml_sys_const_ostype_win32` | `caml_sys_const_ostype_win32_primitive` | `CamlSysConstOstypeWin32.lean:95` |
| `caml_sys_const_ostype_cygwin` | `caml_sys_const_ostype_cygwin_primitive` | `CamlSysConstOstypeCygwin.lean:95` |
| `caml_sys_const_backend_type` | `caml_sys_const_backend_type_primitive` | `CamlSysConstBackendType.lean:95` |
| `caml_int_compare` | `caml_int_compare_primitive` | `CamlIntCompare.lean:172` |
| `caml_sys_argv` | `caml_sys_argv_primitive` | `CamlSysArgv.lean:122` |
| `caml_ml_string_length` | `caml_ml_string_length_primitive` | `CamlMlStringLength.lean:350` |
| `caml_ml_bytes_length` | `caml_ml_bytes_length_primitive` | `CamlMlBytesLength.lean:350` |
| `caml_fresh_oo_id` | `caml_fresh_oo_id_primitive` | `CamlFreshOoId.lean:204` |
| `caml_string_equal` | `caml_string_equal_primitive` | `CamlStringEqual.lean:7` |
| `caml_string_notequal` | `caml_string_notequal_primitive` | `CamlStringNotequal.lean:7` |
| `caml_int64_float_of_bits` | `caml_int64_float_of_bits_primitive` | `CamlInt64FloatOfBits.lean:7` |



`BlockInput` certificates are fully discharged by generated pins/decodes,
register inputs, return alignment and finite shape checks. They are not
assumed as primitive execution premises. `VmPayload` is the memory/world
part of `VmReprAt` at a C-call boundary: `Setup_for_c_call` temporarily changes
sp and PC; the arm's generated restore segment supplies the loop-head register
view. The callee post includes a0, caller return PC, all other non-noise
registers (except a5 as well for comparison), memory, output, `GoodState`,
image pins, runtime and loop registers.

All nine modules build within the default heartbeat budget (about 2 seconds
each). Explicit finite symbolic evaluation avoids a deep kernel reduction in
the max_wosize shift case. Shared payload/root restriction and runtime frame
lemmas compile. The abstraction gate and discipline checks pass. The full
`OCaml.Audit` build passes (1,060 targets); all nine primitive theorems and
shared adapters use only `propext`, `Classical.choice`, and `Quot.sound`.
The full build passes. The audit gate normalizes wrapped axiom lists before applying its unchanged
allow-list, rejects Lean process errors explicitly, and builds the Audit target
so freshly imported audit dependencies cannot be missing.
The nine-primitive milestone passed the full integration gate and is landed; no semantic
changes were made to `primF1Impl`.

## Signed comparison milestone

`tag_toNat`, `tag_toInt`, and `tag_signed_lt` establish signed order for all
63-bit OCaml integers. The generated six-instruction summary returns the
`primF1Impl` comparison value, preserves VM data and the platform, and frames
all registers outside a0/a5 and the machine noise registers.
`ImmediateInput.arguments` records each represented argument in its C ABI
register. `PreservesLoopRegisters [10, 15]` is a discharged finite check.
`register_of_blocks` now supplies the common frame proof for constants,
comparison, and upcoming read-only accessors; `Leaf` reuses it.

## ELF migration coordination

The foreman announced a pending fixed-address `.embed` image migration.
Function addresses stay fixed while data addresses and relative immediates
change. All data references use `Layout`; after that landing, rebase and run
the primitive generators again to refresh pins and per-word decode imports.

## Read-only accessor work

`caml_sys_argv_primitive` compiles against the migrated ELF, with the explicit
`valWord pl s.world.argv = some (word c Layout.sym_main_argv)` precondition.
`VmPayload.accu_of_root` and `readOnly_contract` preserve the heap placement
when returning an existing root; immediate contracts specialize the same rule.

The generated string/bytes length summaries compile in about 2.5 seconds each
within the default proof budgets. Both length instances share `StringInput`/`string_length_contract`;
`StringGeometry` supplies RAM/HTIF exclusion bounds, with data addresses from
`Layout`. `StringInput.shape` derives header size and the final padding count
from the represented live object. `stringLengthWord_tag` proves the tagged
result for arbitrary represented string lengths.

The generator emits literal instruction records certified by `ElfDecode`,
separate code/static certificates, and a load-prefix register checkpoint.
`Control.memory_free_facts` handles register-only spans without inspecting
data operands. `ReadWindow.ld`/`.lbu` package total-byte observations and access
bounds, preventing large scalar-load simplification proofs. `readonly_wlog`
proves the empty write log from instruction syntax. These helpers add no
machine run law or execution premise.

Rebased on the fixed-embed migration `7fa1750` and regenerated the primitive
census and all four primitive generator families. Generator drift, proof
discipline and the abstraction gate pass. All 39,240 pinned bytes match the
ELF. The complete build and axiom audit pass (1,119 targets; standard axioms only). Builds run only with at least 25 GB
available and under the 24 GB cap.

## Mutable-global work

`caml_fresh_oo_id_primitive` returns the old tagged global and stores its
increment, matching `primF1Impl`. The write-effect post generalizes the
read-only register frame, and its VM frame reuses `writeLog_out`,
`FixedBytesLoaded.transport`, and relocation `Eqv.transport` at identity.
`PayloadOutside` describes static separation of the write log from VM
observations; allocator placement and stack/code/global separation will supply
it. The generated six-instruction certificate uses `ReadWindow.ld` and
`WriteWindow.sd`; `counter_contract` connects the exact write log to the
abstract world update. `WindowStable` records the runtime invariant’s
required frame law over the counter window. No execution premise is assumed.

## Current follow-up

The rebase includes the arms lane’s `PrimitiveBindings` repair. Primitive
input/post records now carry this metadata; read-only summaries use its
existing memory frame, while `BindingsOutside` supplies the two table
observations needed for a disjoint write-log frame. All fourteen summaries
and the full axiom audit pass (1,334 targets, standard axioms only).

`PaddedString` records the allocator’s canonical zero padding. The shared
word-to-byte bridge reuses `bytesT_extract` and `Reloc.Copied` to connect the
ELF’s full-word comparisons to abstract string contents.
`PaddedString.eq_iff_words` proves equivalence in both directions, including
length recovery from the final padding-count byte. Both string summaries consume this explicit allocator invariant.

## String scan progress

The binding/canonical-string milestone landed at `2f8530a` after the full gate.
`gen_fn.py --ocaml-string-scan` now emits nine CFG block certificates for
`caml_string_equal`, including both branch outcomes. Fixed-point register
liveness retains the values needed across loop joins. The complete generated
module compiles in 5.5 seconds at the default budgets.

`BoundaryPost` packages a shared read-only ABI/image/register frame;
`boundary_bind` composes generated summaries through the existing triple rule.
`StringScan.scan_iteration`, `scan_loop`, and `scan_words` compile (the loop
module takes 1.9 seconds). They use `loopFromBody`, a decreasing word count,
an equal-prefix invariant, and a mismatch witness. No run induction was added.
The entry paths and the `primF1Impl` bridge are proved and landed.

The entry composition now compiles in 1.1 seconds. Signed load offsets in
the generator use explicit bit-vector subtraction, so existing header-address
lemmas apply without expanding byte values. `string_comparison_value` connects
the complete machine decision to the byte-list equality in `primF1Impl`;
`caml_string_equal_primitive` is the generated represented-call headline.
Next is the stack-writing `caml_string_notequal` call wrapper.

## Inequality call wrapper

`caml_string_notequal` saves ra in a 16-byte native-stack frame, calls
`caml_string_equal`, restores ra/sp, and subtracts the tagged result from 4.
The complete-register call adapter `Vsa.Sim.bridgeOfSegFull` is ported from
upstream commit `1453d2e` (source read only; see ATTRIBUTION.md).
A common `CallInstr`/`CallShape`/`CallDecode` adapter connects generated
ElfDecode and code-pin facts to that bridge. `wrapper_enter`, `wrapper_equal`,
and `wrapper_leave` compose with `FnSummary.callSplice`; the complete
`string_notequal_machine` compiles in 1.4 seconds. `StringNotEqualInput`
records the native stack window, image/payload/table separation, and argument
object separation. `PaddedString.frame_log` preserves the allocator invariant
using `Reloc.Copied`. The represented contract compiles in 16 seconds.
The generated wrapper certificates compile in 1.9 seconds; finite sign-extension
certificates avoid deep normalization of symbolic addresses. No budgets were
raised. The abstraction gate passes (C1=0, C2=7, C3=7, C4=3), as does discipline.


## Allocating primitive follow-up

The next shared component is heap-allocation transport: the old reachable
objects retain their placement and one fresh result object becomes reachable.
The `caml_int64_float_of_bits` tail call enters `caml_copy_double`; its nursery
fast path writes young_ptr, a double header and one payload word. The slow
path calls `caml_alloc_small_dispatch` and needs collector integration. This
primitive remains open; a fast-path lemma alone will not be counted as the
complete primitive.

`VmPayload.allocate` and `allocation_contract` now build. They reuse the
symbolic heap allocation laws and classify post-allocation reachability as
fresh or old; fresh-object fields must point to old live objects. A placement
can reserve its unreachable fresh key before the call. No relocation or run
induction is introduced.

`gen_fn.py --ocaml-allocation` emits both nursery blocks, code pins, scalar
access certificates, exact write-log equations and `FnSummary` folds.
`DoubleAllocation.copy_double_fast` composes the blocks with `summary_bind`
and proves the complete successful nursery path. `double_layout` connects
the exact log to the double object's header and bit payload (253 tag, one word). The collector
branch and the primitive's input/tail-jump bridge remain open, so the total
stays **16/30**. These are reusable support results, not a seventeenth primitive.

Allocation-support validation: full regression and audit pass (1,918 targets;
permitted standard axioms only). Generator drift, discipline and a8 pass.

Allocation support landed at `0c3d49d` after the complete integration gate.

## Named-value model correction

The C runtime (`runtime/callback.c:203–227`) updates the matching root slot;
the former model appended a duplicate. Since `roots` includes `World.named`,
that retained an obsolete value as a GC root. C names also end at the first
NUL byte, whereas the former model used the complete OCaml byte string.
`scripts/validate_named_values.py` probes both cases against the host 4.14.4
runtime through `caml_named_value`: replacement yields 22, and two names
sharing their pre-NUL prefix yield 44. The model transcription now uses
`namedValueKey` and `registerNamedValue`. All ten host/model difftests pass
(`results/bc-named.json`), including the new `f1_named` registration sequence.
The direct host table probe supplements stdout/exit comparison.
`OCaml/Bytecode/NamedValues.lean` proves latest-key lookup, other-key framing,
retained-root membership, and the actual primitive replacement transition. No machine primitive is counted by this repair.

Named-value correction validation: full regression/audit passes (1,965 targets,
standard axioms only); discipline, generator checks and a8 pass.

The named-value correction landed at `d05db1f` through the full gate.

## G1 allocating primitive contracts

PLAN.md §3 selects G1 (no collection after the cut) for the initial F1–F3
refinement. Accordingly, allocating primitive summaries will carry explicit
allocation-room and metadata-separation premises supplied from the budget and
runtime invariant. Their G1 machine summaries do not require completing the
A6 collector branch. The double constructor support is ready; its int64
payload-load/tail-call and represented allocation bridge are being connected.

`int64_float_machine` now composes the generated boxed-payload load and tail
jump with `copy_double_fast`, using `FnSummary.tailJump`. The complete G1
represented allocation contract compiles: `Int64FloatInput` supplies the
represented source object, RAM bound, reserved fresh placement, separation
and nursery room. `AllocationRuntime` is the chosen runtime predicate's
memory-effect frame supplier; no machine execution is assumed by that
premise. The result heap gains exactly `.double bits` and the world is
unchanged. `BoundaryPost.then_write` factors the read-only-prefix/write-log
composition so concrete memory maps remain opaque during elaboration.
The generated headline and full regression/audit pass (2,103 targets, standard
axioms only), with **17/30 G1 summaries proved**. The milestone landed at `8658c0d` through the complete gate; the
collector-enabled extension remains A6.


## Library call adapter

The next library consumers use the landed `SnpW`/`LocalRun` certificates
(strlen, formatting and allocator wrappers). A shared bridge is being built
with `loopFromBody` and the existing machine run-kernel adapters. Its measure
is the least remaining bounded certificate; it introduces no run induction.
The post must retain total-byte/output observations, the facts these library
specs provide, and must not claim exact optional-memory-map equality.

`localRun_triple` and `symbolic_summary` now compile; `strlen_summary`
instantiates the landed `strlen_nw` certificate, retaining return PC, length,
non-scratch registers and unchanged total bytes (`strlen_memory`). Both
modules compile at the default elaboration budget (about one second each).
These are shared support, so the primitive count remains 17/30. The next
step is observational VM framing and the generated string-allocation caller.

Library bridge landed at `21fe0a3`, including the full gate and axiom audit.
`VmPayload.frame_observedLog` now generalizes the existing write-log frame
using `MemEqv` and observable output; `frame_log` remains its exact-map
specialization. `frame_observed` supplies the read-only case. Object and
channel transport still use the existing relocation combinators.
`LibraryFrame.lean` recovers optional ABI/PC values from `VsaOk`, preserves
primitive bindings, and restores exact code pins from byte observations plus
live-memory presence. `strlen_leaf` and `strlen_result` supply the next
generated caller segment's ABI input and length. Focused builds pass.

Observational frames landed at `19470f8` through the full gate. Nursery work
now shares `AccessPlan` and `scripts/syi/ocaml_nursery.py`: generated
`SmallAllocation` reserve/initialize and `StringAllocation`
prepare/reserve/initialize block summaries compile from this ELF. String
initialization's internal fallthrough split is merged along the selected
nursery path. Concrete string-prefix stack/size facts are in progress;
reservation, padding layout and caller composition remain open. No new
primitive is counted by these block certificates.

The three string block effect theorems now compile: `prepare_fast`,
`reserve_fast`, `initialize_fast`. `prepare_access` and `reserve_access`
discharge scalar accesses from explicit RAM/write windows and total load
pins. Initialization still takes its finite `AccessPlan`; discharge of that
plan, whole-constructor composition and string layout remain next.
The initialization write log required small explicit constant certificates
instead of eager global simplification; no budget increase was used.
Discipline and abstraction checks pass (C1=0, C2=7, C3=7, C4=3).

Nursery block certificates landed at `5984250`. The complete
`alloc_string_nursery` function summary now composes all three blocks and
restores native `sp`, retaining the exact combined write log.
`initialize_access` supplies all six scalar accesses from RAM/write windows
and post-store pins. `nursery_readback` discharges those post-store reads
from `NurseryMetadata` plus stack/header/metadata separation, without an
execution premise. Focused builds pass at the default budget.

Next: string header/padding layout, the copy-string caller, and full memcpy.
The existing local `MemcpySpec` only certifies the byte-loop entry; upstream
`syi-absint-merge` at `1453d2e1` also has `MemcpyLoops.memcpyLocalRun` covering
dispatch/alignment/word/bulk/byte paths. Reuse and retarget that proof for the
caller instead of limiting executable names to the short byte-copy path.
The primitive count remains 17/30 until represented caller contracts land.

The complete nursery constructor/readback support landed at `74e6126`
(after one fast-forward race and a repeated successful gate). Full memcpy
is being ported through the existing allocator-template generator, with
its source interpreter import dependencies cut at pure byte facts. The
source is read-only `syi-absint-merge` commit `1453d2e1`; provenance is in
ATTRIBUTION.md. Constructor string layout and copy-string caller remain
open alongside that port.

Full memcpy now compiles at the default budget (loop module about 21s,
`memcpy_summary` bridge about 1.4s). `image_local` recovers exact immutable
code pins from the confined write frame and live-byte presence. The bridge
returns `LeafInput`, represented copy bytes and the complete observational
frame. The import cut now reuses `MemcpySites2.ldData8`, avoiding a duplicate
definition in `LibraryByteFacts`; its users remain source-generated.
Discipline and a8 pass unchanged. This closes library support, not a new
primitive count. Next is the string layout/copy-string represented caller.


2026-10-02 resume: full memcpy landed at `6d1b6b7`; rebased on current
main and regenerated every F1 family, census and library template. The
fixed-embed ELF migration is included and regeneration introduces no drift.

Library composition now preserves presence through generated writes:
`LibraryEffects.lean:10` (`RegistersPost.vsaOk`) reuses the existing write-log
presence and register frame laws. `StringNursery.NurseryPost` retains this
invariant universally for any caller-supplied live-byte set; no additional
execution assumption was introduced. The previously private
`VsaIris.Inst.gpr_avoids_noise` certificate is public for reuse.

`StringAllocationArithmetic.lean` proves word count, rounded span, header
encoding and padding subtraction at the default budget. `StringAllocationLayout.lean`
proves `shell_layout` from the canonical three-store log, then
`StringShell.object` and `.padded` complete the representation once the
payload bytes are supplied. Splitting the write log explicitly avoids a
unification timeout without changing any proof budget. Focused builds pass.

Still 17/30 primitive summaries. Next: relate the actual initializer log to
`shellLog`, preserve the shell across the confined memcpy write, generate the
copy-string caller boundaries and compose the executable-name primitive.

The actual initializer log is now normalized by `initialization_shell_log`
(`StringConstructorLayout.lean:9`), and `NurseryPost.shell` supplies the layout
directly from the machine constructor's postcondition. `StringShell.frame_payload`
preserves header/padding across a copy confined to the data bytes. The full
1974-target audit rebuild passed; the final layout bridge is included in the
next audit. Next is the generated copy-string call composition.


String layout/invariant support landed as `55667f5`. The copy-string generator
now emits four CFG boundary certificates and all three direct-call pins,
shapes and ElfDecode adapters. `ocaml_block_certificates.emit_block` is shared
with the nursery generator; its existing outputs are byte-for-byte unchanged.
`StringCopyFast.{save,size,arguments,restore}_fast` supply the four boundaries
from stack windows and memory pins, with exact effects and register interfaces.
All focused builds pass without increased budgets. The whole copy-string
composition and represented primitive contract are next; the count is 17/30.


Copy-string boundaries landed at `c0f2125`. The actual composition now covers
entry through `strlen` (`StringCopySized.copy_string_sized`), the length store,
the allocation JAL, and the complete G1 constructor
(`StringCopyAllocated.copy_string_allocated`). It returns the allocated shell
at the memcpy-argument boundary. `caller_readback` proves all three native
save slots from the combined write log and explicit later-store separation.

Shared adapters now expose generated GPR/RO frames and transport total-byte
equality through write logs. `strlen_call` instantiates the landed symbolic
reader at actual caller register observations. `NurseryGeometry` separates
static RAM/guard/image conditions from per-state inputs, and the constructor
post retains the restored `ra`. Focused builds all pass. The next step is
memcpy plus restore, then the executable-name tail and represented allocation
contract. The primitive count remains 17/30 until that contract is landed.


The complete native string copy now composes all three calls and the return:
`StringCopy.copy_string_finish` and `StringCopy.copy_string_machine` preserve
byte observations, the string shell, ABI registers and the native stack.
The generated executable-name tail loads `Layout.sym_caml_exe_name`.
`executable_name_contract` extends the represented heap with its copied bytes,
frames the old payload/bindings and preserves the running platform. Explicit
G1 nursery-room, placement/separation and memory-observation runtime premises
are supplied by callers; none assumes execution or the desired postcondition.
`MemoryFrame` now supports pointwise footprint frames while retaining its old
exact/observational log APIs. Focused builds pass at default proof budgets.

| Primitive | Theorem | Location |
| --- | --- | --- |
| `caml_sys_executable_name` | `caml_sys_executable_name_primitive` | `CamlSysExecutableName.lean:7` |
| `caml_sys_get_argv` | `caml_sys_get_argv_primitive` | `CamlSysGetArgv.lean:7` |
| `caml_sys_get_config` | `caml_sys_get_config_primitive` | `CamlSysGetConfig.lean:7` |

Next: allocating configuration/argv and channel primitives, named-value
registration, output/formatting and process exit. The exit remains 30/30 landed
and audited; this milestone does not close the lane.

Small-block nursery composition is next, shared by configuration/argv tuple
allocation. The generated two-block certificates already exist; register
evaluations and scalar effect adapters are under construction.


`SmallAllocation.alloc_small_nursery` (`SmallNursery.lean:45`) now proves
reservation, header initialization and return for the G1 path. It exposes
an exact two-store log, preserves the return address, and transports the
library presence invariant. `blockHeader_ok` and `NurseryPost.header`
(`SmallLayout.lean:17,26`) connect its initialized header to object layout.
The two generated blocks share scalar access-plan/effect adapters in
`SmallFast.lean`; all focused builds pass at default budgets.

The argv-pair caller now has three generated boundary summaries and two
JAL adapters in `ArgvTuple.lean`. Call-pin emission moved into the shared
`ocaml_block_certificates.emit_call`; existing string-copy artifacts remain
byte-for-byte unchanged. Full caller composition and represented two-object
allocation are still open. No additional primitive is counted (18/30).
Discipline and a8 pass: C1=0, C2=7, C3=7, C4=3.


Small allocation and argv boundaries landed as `2826b17`, after a complete
gate and one push race. The three argv boundary effect wrappers now compile
in `ArgvTupleFast.lean`. Generated store-log certificates use bounded chunks
and `Vsa.Sim.wlogM_append`; unrestricted simplification of the full stack log
caused rapid memory growth, so those exact processes were stopped and the
proof was factored. Raw base-plus-offset addresses and definitional store
certificates keep the checked replacement within the default budgets.

`SizedMemory`, `AllocateMemory`, and `CopyMemory` separate static memory
requirements from dynamic leaf/stack/library entry facts. The existing
`CopyInput` interface remains compatible, and the executable-name contract
rebuilds successfully. Next is full argv call composition and its represented
two-object allocation; the landed primitive count remains 18/30.
