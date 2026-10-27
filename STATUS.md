# Foreman status

Updated 2026-10-27 22:38 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

`origin/main` is **`2ee3051b`**, verified remotely. The full gate passed
**6,064 build jobs**, **9,169 allowed-axiom reports**, all generator/ELF
checks and **329 OS traces** (5,069 steps, 324 accepted, 5 special,
zero rejected or unsupported). Integration log:
`/tmp/syo-allocator-counted-search-integrate.log`.

This batch closes the captured allocator/`libHeap` premise, removes its
obsolete generated-table argument, supplies counted interpreter entry and
shared loop/placement continuation, and composes G2 bitmap search through
the native allocation return. A captured heap certificate is not reset
execution. The native G2 return alone is not full allocator preservation.

Earlier full-gate batches: initialized string and G2 split/complete route
`88d4c057`; first root insertion and decimal vsnprintf `333e9614`;
complete counted channel returns `71547e46`; named ownership `7e7a052a`.

## Next landing batch

Reviewed and committed locally; the next full gate is running in
`syo-wt/a6-gc-next2` with coherent caches from the published batch:

- `e97aaed4`: shared counted RuntimeFrame and 58 stack/load/assignment/trap
  wrappers. 3,194 affected jobs and 137 focused allowed-axiom reports pass.
  Together with CONST0/NEGINT this gives 60/134 counted opcode rows;
  the exact remaining 74 are listed in `docs/lanes/a1-prims.md`.
- `c100f1f0`: actual backtrace/root registration through first insertion,
  returning to `0x80004e84`, with domain/page-table/root-value frames.
  3,436 affected jobs; 3,440-job audit build (56 backtrace and 311 insertion
  declarations); all 2,045 startup generator outputs reproduce.
  Review found that the exported stack/atom existential had dropped its
  nested ELF-reset witness. The stronger interface is being checked now.
- `8f60fb69`: actual G2 returned small-list/header/bitmap representation
  and allocated-block separation, from explicit original physical extents.
  1,288 affected jobs; 239 allowed-axiom reports and two axiom-free
  declarations. Preservation of the new `SmallPhysical` component itself,
  and its production by native callers, remain open for repeated allocation.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Startup Sol | Retain ELF-reset identity and expose universal reset-to-backtrace | `syo-wt/a0-boot-next` |
| Counted-allocation Sol | Lift nursery/native allocation frames and allocating rows | `syo-wt/a1-prims-next` |
| Lead | Gate counted-stack/backtrace/G2 representation; review remaining suppliers | main; `syo-wt/a6-gc-next2` |

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
and a repair tied to the actual caller ledger. This is currently a contract
inspection, not a checked counterexample or a claim of global inconsistency.

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
named reserves and G2 physical preservation. No user-only decision blocks work.
