# Foreman status

Updated 2026-10-28 15:05 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains G2; `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes. Its draft is preserved.
- Separate Sol CLI workers, high reasoning, at most two. Worker/build scopes
  have a 12 GB cap; check available memory before launch. Use the build guard.
- The lead reviews, commits and lands through `scripts/integrate.sh`, using
  normal pushes to `origin/main`. Preserved work is on `keep/*` branches.
- Read `docs/lanes/DEAD-ENDS.md` before assigning a route again.

## Published

`origin/main` is **`804538a50bb3f1a615a9bfe48a3779ada1b046aa`**, verified remotely.
The full gate passed **6,090 build jobs**, **9,360 allowed-axiom reports**
and 129 axiom-free reports, generator/ELF checks and **329 OS traces**
(5,069 steps, 324 accepted, 5 special, zero rejected or unsupported).
Logs: `logs/integrate-804538a5.log`, `logs/build-804538a5.log`.

## Latest landed proofs

- `0f5ecaef`: G2 physical free-extent bounds and separation preserved through
  actual pop/split/remnant allocation, returning combined SmallRepresentation.
  Original dispatch/caller production and other cases remain open.

- `e35aa58b`: counted allocation frames, seven opcode rows and three allocating
  primitive return contracts. The ordinary counted census is **67/134**.
  Complete C_CALL composition remains open.
- `b49f9173`: actual ELF-reset witnesses retained through stack, atom and
  backtrace producers, with universal reset-to-backtrace reachability.
  The continuation from backtrace to `Loaded` remains open.
- Previous batch `e12e1731`: counted stack RuntimeFrame and 58 wrappers,
  native backtrace/root registration, G2 returned list/header/bitmap
  representation and allocated-block separation.
- Earlier `2ee3051b`: captured allocator/`libHeap`, counted interpreter
  entry/loop and G2 bitmap-search return. Captured memory is not reset execution.

## Latest published batch

`da1ab268` proves the plain signed decimal native alloc_sprintf entry-to-original-return,
with exact byte-string representation, saved ABI, observable output and explicit
runtime/frame conditions. Its 1,412-job affected build passed. Lead verified
all 16 new theorem registrations and 28 allowed focused axiom reports.
General formatting and C_CALL2 remain open. It passed the full gate with `58740097` in published `804538a5`.

`58740097` repairs custom-state ownership using the selected caller ledger,
with a checked captured empty-ledger obstruction and actual startup/frame/
opening/listing consumers. Recovery passed 3,653 affected jobs and 60 focused
audits (59 standard, one axiom-free); all 19 new theorems are registered.
Full physical Customs and the separate global-frame compatibility issue
remain open. The gate cache transfer from the idle custom lane checked
toolchain/manifests/dependency trees and held both build locks.

## Reviewed for the next gate

The next batch includes `9de2d983` (122 counted rows), `2e47e2fc`
(local custom-space repair), `9549edb8` (field and empty-growth frames),
`4f827ee5` (actual counted insertion separation; 129-row table) and
`d1314b91` (original best-fit entry through next-size allocation return).

The combined spatial/custom/count consumers passed 3,664 affected jobs and
57 focused audits, covering both new and all 15 changed declarations.
G2 passed 1,290 jobs and 260 audits (258 standard, two axiom-free), including
all nine new theorems. Lead independently checked coverage and allowed sets;
proof rebases were clean, and both adjacent lane-log entries were retained.
Evidence is archived in `logs/counted-spatial-*` and `logs/a6-entry-next-*`.
Reviewed snapshots remain on `keep/*` branches. Full integration is next;
none of these five proof commits is yet published.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| C_CALL Sol | Actual counted C_CALL1/2 successes for 19 ordinary primitive names | `syo-wt/a6-gc-next2` |
| Startup Sol | Universal reset through null-interpreter/debugger initialization | `syo-wt/a1-prims-next` |
| Lead | Full combined gate, then concrete custom runtime supplier review | main; `syo-wt/bprime` |

Two replacement Sol CLI tasks are queued after review, under the same 12 GB
caps and memory checks. G2's next-size entry result is in the gate batch;
remaining allocator routes and full growth continue in subsequent slots.
No user-only decision blocks work.

## Remaining F1 boundaries

The reviewed counted table has **129/134** supplied rows relative to named
`CustomMemCall` and G2 full growth. `LibHeapAt.refCustomApart` derives the
remembered-storage/custom separation from actual selected `CustomSpace`;
no extra arbitrary spatial supplier remains. Full growth still requires
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`;
the base-layout boundary cannot silently supply counted return facts.

C_CALL1–5 remain whole-row obligations. Native opening/listing returns exist,
but their concrete runtime, heap/record and after-call suppliers remain open.
Physical custom accounting also needs concrete startup/read-context producers;
table occupancy alone is insufficient. Selected ownership and local spatial
invariants replace the old universal ledger/global record laws. Their checked
obstructions are conditional memory-contract results, not reachable executions
or claims of global inconsistency. Combined affected consumers have passed;
the full gate is pending.

Named registration needs a proved node/key reserve and repeated root-cell
removal/reuse accounting. Distinct immutable names alone do not bound all
skiplist allocation calls. The owned named ledger is already carried.

The complete decimal native wrapper is checked locally. Formatting still
needs general `d/i/u/x/X/o` flags/width/precision, large/major allocation,
reachable caller/runtime suppliers and the C_CALL2 return. Do not narrow GoodF1 to make those premises vanish.

Reset still needs the continuation after backtrace through interpreter/debugger
initialization, code/primitives/data loading, system/argv setup and `Loaded`.
G2 still needs original physical-invariant production and remaining dispatch,
other size classes/colors, complete allocator readiness and collection.
The a2-sem uncaught-path WIP stays preserved and lower priority: GoodF1
excludes that path.

Task packets are in `tasks/sol-*.md`. Next priorities are
concrete custom startup/read-context suppliers, ordinary counted C_CALLs,
console continuations, general formatting, named reserves and G2 original
small-allocation dispatch. The concrete null-interpreter/debugger
continuation to `0x80004e94` is queued in `sol-reset-interp-init.md`. No user-only decision blocks work.
