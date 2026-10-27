# Foreman status

Updated 2026-10-27 23:06 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

`origin/main` is **`e12e1731`**, verified remotely. The full gate passed
**6,083 build jobs**, **9,292 allowed-axiom reports**, all generator/ELF
checks and **329 OS traces** (5,069 steps, 324 accepted, 5 special,
zero rejected or unsupported). Archived logs:
`logs/integrate-e12e1731.log`, `logs/build-e12e1731.log`.

The latest batch adds the counted stack RuntimeFrame and 58 opcode wrappers,
actual backtrace/root-registration execution, and G2 returned free-list,
header and bitmap representation with allocated-block separation. It does
not yet export the stronger reset-qualified interface or preserve the new
G2 `SmallPhysical` component for repeated allocation; those are next.

The previous `2ee3051b` batch closes the captured allocator/`libHeap` premise,
counted interpreter entry/loop placement and native G2 bitmap-search return.
A captured heap certificate is not reset execution.

Earlier full-gate batches: initialized string and G2 split/complete route
`88d4c057`; first root insertion and decimal vsnprintf `333e9614`;
complete counted channel returns `71547e46`; named ownership `7e7a052a`.

## Latest landed proofs

The verified batch contains:

- `e97aaed4`: shared counted RuntimeFrame and 58 stack/load/assignment/trap
  wrappers. 3,194 affected jobs and 137 focused allowed-axiom reports pass.
  Together with CONST0/NEGINT this gives 60/134 counted opcode rows;
  the exact remaining 74 are listed in `docs/lanes/a1-prims.md`.
- `c100f1f0`: actual backtrace/root registration through first insertion,
  returning to `0x80004e84`, with domain/page-table/root-value frames.
  3,436 affected jobs; 3,440-job audit build (56 backtrace and 311 insertion
  declarations); all 2,045 startup generator outputs reproduce.
  The original exported stack/atom existential dropped its nested ELF-reset
  witness; reviewed follow-up `b49f9173` now supplies the stronger interface.
- `8f60fb69`: actual G2 returned small-list/header/bitmap representation
  and allocated-block separation, from explicit original physical extents.
  1,288 affected jobs; 239 allowed-axiom reports and two axiom-free
  declarations. Preservation of the new `SmallPhysical` component itself,
  and its production by native callers, remain open for repeated allocation.

## Reviewed for the next batch

`e35aa58b` supplies counted allocation frames, seven opcode rows and three
allocating primitive return contracts. Both final affected builds passed
3,626 jobs; 32 focused reports use only the allowed axioms, and all 27 new
theorems are registered. The ordinary counted census is now 67/134 locally;
the primitive contracts still need complete C_CALL composition. This batch
will be gated with the stronger reset interface.

`b49f9173` retains actual ELF-reset witnesses through stack, atom and backtrace
producers and proves universal reset-to-backtrace reachability. The affected
build passed 3,436 jobs; its 3,439-job audit build reports all 78 focused
declarations and 1,026 allowed reports. The actual continuation from backtrace
to `Loaded` is explicitly open. Both changes are in the next full gate in `syo-wt/bprime`. The cache
handoff from the idle startup lane checked toolchain/manifests/dependency
trees and held source/read and destination/write build locks.

## Reviewed behind the active gate

`0f5ecaef` preserves G2 `SmallPhysical` through the actual pop/split/remnant
route and returns a combined small-list representation. The affected build
passed 1,289 jobs; all 251 focused audit reports are present and allowed
(249 standard-axiom reports, two axiom-free). Native initialization/caller
production, original dispatch and the other allocator cases remain open.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Formatter Sol | Compose decimal alloc_sprintf entry-to-return | `syo-wt/a6-gc-next2` |
| Custom-ownership Sol | Repair universal-ledger assumption with selected ownership | `syo-wt/a1-prims-next` |
| Lead | Gate allocation/universal reset; review remaining suppliers | main; `syo-wt/bprime` |

## Remaining F1 boundaries

Ordinary uncounted opcode families and interpreter entry/halt composition
exist. The counted table still needs its remaining allocation, control,
barrier and primitive frames/rows and complete C_CALL assembly. Opening and
out-channel listing use checked native returns, but their concrete runtime,
heap/record and after-call suppliers remain open. Table occupancy alone is
not the full physical `Customs` predicate: resource words and the current
domain's table identity need startup/frame/call producers.

Lead review also flagged `CallerApart.free`, which quantifies over every
heap ledger although `HeapReady` does not require a ledger to be exhaustive.
`sol-custom-ledger.md` asks for the precise captured empty-ledger obstruction
and a repair tied to the actual caller ledger. The worker has checked the empty-ledger obstruction and is validating the
selected-ownership repair. A separate lead inspection found a candidate
incompatibility between the global record-separation law and unrestricted
outside-byte framing; `sol-custom-apart-local.md` queues a checked conditional
obstruction and local spatial-invariant repair. That second candidate is
not yet a proved defect or a claim of global inconsistency.

Named registration needs a proved node/key reserve and repeated root-cell
removal/reuse accounting. Distinct immutable names alone do not bound all
skiplist allocation calls. The owned named ledger is already carried.

Formatting still needs the complete decimal native wrapper, general
`d/i/u/x/X/o` flags/width/precision, large/major allocation and the C_CALL2
return. The checked decimal vsnprintf and initialized-string splice do not
close general formatting. Do not narrow GoodF1 to make those premises vanish.

Reset still needs the continuation after backtrace through interpreter/debugger
initialization, code/primitives/data loading, system/argv setup and `Loaded`.
G2 still needs original physical-invariant production/preservation, dispatch,
other size classes/colors, complete allocator readiness and collection.
The a2-sem uncaught-path WIP stays preserved and lower priority: GoodF1
excludes that path.

Task packets are in `tasks/sol-*.md`. Next priorities include selected custom
ownership, counted control/console continuations, decimal formatter return,
named reserves and G2 physical preservation. The concrete null-interpreter/debugger
continuation to `0x80004e94` is queued in `sol-reset-interp-init.md`. No user-only decision blocks work.
