# Foreman status

Updated 2026-10-28 16:47 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains G2; `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes.
- Separate Sol CLI workers, high reasoning, at most two. Each worker/build
  scope is capped at 12 GB; check 25 GB available before launch. Use the guard.
- Lead reviews, commits and lands through `scripts/integrate.sh`, with normal
  pushes to `origin/main`. Preserve reviewed snapshots on `keep/*` branches.
- Read `docs/lanes/DEAD-ENDS.md` before assigning a route again.

## Published

`origin/main` is **`34658c244a0fd1ec4c6020f0a64d21a781504821`**, verified remotely
after the full gate exited at 16:46 UTC. It passed **6,146 build jobs**,
**9,634 main allowed-axiom reports** (9,638 including TCB), 133 axiom-free
reports in the gate transcript, generator/ELF checks and **329 OS traces**
(5,069 steps, 324 accepted, 5 special, zero rejected or unsupported).
All build dependency reports also use only allowed axioms. Evidence:
`logs/{integrate,build}-34658c24.log`, `logs/gate-34658c24.json`.

This batch publishes:

- `319f74d2`: four counted console returns and complete C_CALL4. The actual
  native windows preserve physical counts and per-record refs/links while
  buffers and offsets change; returned placement comes from native return
  evidence. The complete counted census is now **132/134**, with C_CALL1/2
  remaining. Lead checked all 36 new unique registrations, 2,372/3,713-job
  builds and 47 focused reports (46 standard, one pure).
  Snapshot: `keep/counted-console-reviewed-20261028`; `logs/console-counts-*`.
- `e99a7397`: original-entry exact/next-size small-success dispatch for
  positive requests <=16 with a suitable represented small list. Actual
  returns retain SmallRepresentation, physical separation, header, ABI and
  exact effects; natural counter credit remains explicit. Lead checked all
  27 new registrations, 1,291-job build and 287 focused reports (285
  standard, two pure). Snapshot: `keep/g2-exact-small-reviewed-20261028`;
  `logs/a6-exact-entry-*`. Remaining large cases/caller production are open.

The preceding `004b521c` published reset through interpreter/debugger to
`0x80004e94` and complete C_CALL3/5; its 6,141-job gate passed. It preserves
actual reset/descriptor/fd/argv ancestry, native steps and runtime/heap frames;
CODE/PRIM/DATA loading and Loaded are still open. Proof snapshots and
`logs/{interpreter-init,ccall35}-*` remain archived.

Earlier gates `51c9653c`, `dfbaf165` and `804538a5` published ordinary counted
primitive returns, selected custom ownership/spatial and barrier frames,
initial G2 next-size dispatch and plain decimal formatting. Their raw gate
and focused logs remain archived. `7047b3cd` isolates fd-2 seek probes so
validation cannot overwrite integration log headers; later full gates pass.

## Reviewed for the next gate

`9b490e19` supplies original-entry counted fresh-OO-ID success and actual
native C_CALL1 halt. The counter frame uses the selected heap and physical
counts; halt projects the counted relation and reuses pinned native exit.
Whole C_CALL1 still needs complete unary success coverage. Lead checked
all nine new unique registrations, 3,291/3,715-job builds and 77 focused
reports (75 standard, two pure). Rebase was clean.
Snapshot: `keep/counted-counter-exit-reviewed-20261028`;
evidence: `logs/counted-fresh-exit-*`. This result is not yet published.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| G2 Sol | Original-entry least-large split and returned physical representation | `syo-wt/a6-gc-next2` |
| Runtime Sol | Listing entry/runtime contract and concrete custom allocation credit | `syo-wt/a1-prims-next` |
| Lead | Gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

G2 started at 16:44 UTC from `9b490e19`; log:
`/tmp/syo-gc-large-split-entry-launch.log`. It is checking the unconstrained
high-bitmap-bit gap before deriving native zero filtering. The packet covers
only request<=16 and the existing sufficiently-large source branch.
Listing started at 16:15 UTC from `a1be6936`; log:
`/tmp/syo-outlist-runtime-local-launch.log`. Its actual setup/entry and
custom-table request/credit components build; returned runtime is in progress.
No worker cache is copied while that worktree is building.

## Remaining F1 boundaries

The published **132/134** table is relative to named `CustomMemCall` and
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`.
The base-layout G2 contract cannot supply the extra returned counts.

C_CALL1 needs concrete opening/listing runtime producers and composition of
all unary successes; reviewed counter and exit cover those branches.
C_CALL2 needs named registration and general formatting. Named registration
must derive node/key reserve from immutable source provenance, including
fully initialized partialBytes, and account separately for repeated root-cell
removal/reallocation. Fixed name/count guards are absent from GoodF1.
Formatting still needs full grammar/printf conversions, flags/width/precision,
large-result allocation and actual caller/runtime suppliers.

Custom allocation needs concrete input credit and returned spending on the
same selected heap; an existential HeapReady capacity alone supplies neither.
Full physical Customs needs actual table-shape/startup/read-context producers.
Captured count observations are not reset execution, and current Loaded alone
does not supply counted_entry_of_custom's initial physical-count witness.

Reset-to-Loaded still needs CODE/PRIM/DATA loading, promotion and system/argv.
The next actual native call is caml_seek_optional_section; retained ancestor
Steps alone do not frame its descriptor/file memory into the current state.
Ready packets cover this seek, opening runtime, physical custom state, general
format parsing and named reserve. G2 also needs remaining tree/size/color
cases, caller invariant production, full allocator readiness and collection.
No user-only decision currently blocks work.
