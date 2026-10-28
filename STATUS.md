# Foreman status

Updated 2026-10-28 14:44 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

`9de2d983` adds the remaining ordinary control/memory/raise/halt families,
with a complete partial row supplier and kernel-checked **122/134** census.
Its original 3,494-job affected build and 130 focused audits passed (129
standard, one axiom-free); lead verified all 122 new theorem registrations.
Rebase retained both audit sets and ledger updates. Combined validation
against the selected-ledger change is still due. Published `804538a5` does not include these new rows.

## Recovery work

Both Sol workers stopped on a usage limit on October 27. Their proof edits
are preserved in `keep/custom-ledger-recovery-20261028` (`ea24267b`) and
`keep/decimal-native-recovery-20261028` (`7f9b7f7d`). Neither checkpoint itself is claimed landed; the reviewed decimal patch is `da1ab268`.
The selected-ledger affected build passed 3,628 jobs; the decimal native
composition passed 1,403. Sol availability was restored on resumption. Both recovery tasks are complete;
the reviewed patches passed the full gate in `804538a5`. Original snapshots remain preserved.

| Slot | Target | Worktree |
| --- | --- | --- |
| Write-row Sol | Seven counted field/global write and barrier rows | `syo-wt/a6-gc-next2` |
| Custom Sol | Conditional global-frame obstruction and local separation repair | `syo-wt/a1-prims-next` |
| Lead | Review local separation/write results; gate counted control | main; `syo-wt/bprime` |

## Remaining F1 boundaries

The write-row worker identified missing dynamic remembered-storage/custom
separation in its baseline (`RefCustomApart`). The parallel `CustomSpace`
repair covers those actual blocked extents. Their results must be composed
to produce that separation from the selected heap, not retain a new
arbitrary spatial premise in the final row supplier.

Ordinary uncounted opcode families and interpreter entry/halt composition
exist. The reviewed counted table has 122 rows; seven write/barrier rows and five
complete C_CALL rows remain, with primitive frames and C_CALL assembly. Opening and
out-channel listing use checked native returns, but their concrete runtime,
heap/record and after-call suppliers remain open. Table occupancy alone is
not the full physical `Customs` predicate: resource words and the current
domain's table identity need startup/frame/call producers.

Lead review also flagged `CallerApart.free`, which quantifies over every
heap ledger although `HeapReady` does not require a ledger to be exhaustive.
`sol-custom-ledger.md` asks for the precise captured empty-ledger obstruction
and a repair tied to the actual caller ledger. The empty-ledger obstruction and selected-ownership consumers are now
checked and reviewed in `58740097`. A separate lead inspection found a candidate
incompatibility between the global record-separation law and unrestricted
outside-byte framing; `sol-custom-apart-local.md` queues a checked conditional
obstruction and local spatial-invariant repair. The conditional
`global_records_frame_obstruction` now builds in the worker tree: readiness,
a bounded pinned domain and a retained minor-resource byte contradict the
old global record law plus arbitrary outside-write framing. This is neither
a reachable execution nor a claim of global inconsistency. The worker is
checking a local `CustomSpace` replacement for actual records/named roots;
its full consumer validation and audit are still pending.

Named registration needs a proved node/key reserve and repeated root-cell
removal/reuse accounting. Distinct immutable names alone do not bound all
skiplist allocation calls. The owned named ledger is already carried.

The complete decimal native wrapper is checked locally. Formatting still
needs general `d/i/u/x/X/o` flags/width/precision, large/major allocation,
reachable caller/runtime suppliers and the C_CALL2 return. Do not narrow GoodF1 to make those premises vanish.

Reset still needs the continuation after backtrace through interpreter/debugger
initialization, code/primitives/data loading, system/argv setup and `Loaded`.
G2 still needs original physical-invariant production/preservation, dispatch,
other size classes/colors, complete allocator readiness and collection.
The a2-sem uncaught-path WIP stays preserved and lower priority: GoodF1
excludes that path.

Task packets are in `tasks/sol-*.md`. Next priorities are composing local custom separation into counted writes,
concrete custom startup/read-context suppliers, ordinary counted C_CALLs,
console continuations, general formatting, named reserves and G2 original
small-allocation dispatch. The concrete null-interpreter/debugger
continuation to `0x80004e94` is queued in `sol-reset-interp-init.md`. No user-only decision blocks work.
