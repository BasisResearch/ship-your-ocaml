# Foreman status

Updated 2026-10-28 14:48 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

- `9de2d983`: 122/134 counted ordinary rows and exact partial-table census;
  3,494 affected jobs, 130 focused reports, 122 new declarations registered.
- `2e47e2fc`: checked conditional global record/frame obstruction and local
  `CustomSpace` replacement for actual records, named roots and remembered
  storage. Startup/frame/native-return producers retain full custom ledgers.
  3,653 affected jobs, 57 allowed reports, all 23 new theorems registered.
  The native `CustomMemCall` stays named, with its physical obligations explicit.
- `9549edb8`: counted field/empty-growth frames, supplied OFFSETREF and six
  conditional barrier rows. Supplied census is **123/134**; six barrier rows
  still need the spatial supplier and the stronger counted G2 full-growth
  instantiation. 2,625 focused jobs, 3,631 affected jobs, isolated 3,244-job
  whileMin check; 55 audited reports (53 standard, two axiom-free), covering
  all 48 added/refactored declarations.

Lead reviewed the evidence and retained audit/ledger updates through rebases.
Proof files merged cleanly; combined validation is due. Original reviewed
snapshots remain on `keep/custom-space-reviewed-20261028` and
`keep/counted-fields-reviewed-20261028`; previous recovery branches remain.
Published `804538a5` contains none of these three later proof commits.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Write-row Sol | Derive RefCustomApart from selected CustomSpace and close row suppliers | `syo-wt/a6-gc-next2` |
| G2 Sol | Original bf_allocate dispatch through larger-small-list allocation return | `syo-wt/a1-prims-next` |
| Lead | Review merged contracts; stage combined validation and next full gate | main; `syo-wt/bprime` |

Both prior workers finished successfully for review. Two replacement Sol CLI
workers run at high effort under separate 12 GB scopes, launched after memory
checks. No user-only decision blocks work.

## Remaining F1 boundaries

The write-row worker identified missing dynamic remembered-storage/custom
separation in its baseline (`RefCustomApart`). The parallel `CustomSpace`
repair covers those actual blocked extents. Their results must be composed
to produce that separation from the selected heap, not retain a new
arbitrary spatial premise in the final row supplier.

Ordinary uncounted opcode families and interpreter entry/halt composition
exist. The reviewed counted table has 123 supplied rows; six barrier rows and five
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
a reachable execution nor a claim of global inconsistency. The local `CustomSpace` replacement and its consumers are checked in
`2e47e2fc`; post-merge validation with the counted write changes is pending.

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
