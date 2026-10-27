# Foreman status

Updated 2026-10-27 22:04 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains with G2; `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes. Its draft is preserved.
- Separate `codex exec` Sol workers, high reasoning, at most two. Every worker
  and Lean build has a 12 GB systemd cap; check available memory before launch.
- The lead reviews and commits; all landings use `scripts/integrate.sh` and
  normal fast-forward pushes to `origin/main`. Known failed routes are in
  `docs/lanes/DEAD-ENDS.md`.

## Landing train

Published `origin/main` is `88d4c057`: initialized-string nursery return,
short formatter allocation splice, G2 split/remnant and complete pick/pop/split
route. The full gate passed 6,056 jobs, 8,595 allowed-axiom reports, all
generator/ELF checks, and 329 OS traces (zero rejected). The gate exposed an
old executable-name rewrite after the shared copy-post refactor; its explicit
adapter repair passed 2,010 jobs before the successful full rerun.

Earlier batches: insertion/formatter `333e9614` (6,049 jobs, 8,510 reports),
complete counted channel returns `71547e46` (6,038 jobs, 8,476 reports), and
physical named ownership `7e7a052a`, all through the full gate.

The next batch contains the captured allocator certificate `d959451a` and
its generated-table consumer update `d890bf6a`. Counted-loop continuation
`274e994b` passed 3,694 jobs and 39 focused reports at its worker base.
The merged allocator composition `16da258b` passes 3,649 jobs and the same
39 focused audits; its counted whileMin entry has no heap premise.
The two boot-read extensions merged and reproduce through their generator.
The same batch also contains checked G2 bitmap-search composition
`4eec805d`: 1,287 affected jobs and 217 audited declarations. Its original
list/map facts produce the selected size/head and saved native frame.
These results are not yet published. Prior WIP and reviewed tips remain
preserved on `keep/*` branches.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Counted-stack Sol | Reuse generic stack-writing rows with actual count frames | `syo-wt/a1-prims-next` |
| Startup Sol | Extend actual reset execution through backtrace/root registration | `syo-wt/a0-boot-next` |
| Lead | Full gate for allocator, counted continuation and G2 search | main; `syo-wt/a1-prims-next`, `syo-wt/bprime` |

The first G2 split attempt reached the 12 GB cgroup cap while building
`BestFitNext`, after its generated split module passed 609 jobs. WIP is
preserved (`keep/gc-split-20261027-2057`), and the resumed worker isolated
the expensive declarations under a 6 GB diagnostic limit. The checked result
`ecca3e24` passes 1,264 affected jobs and 180 standard-axiom reports, with
generator and discipline checks. Bounded scalar/log/access certificates
replace the failed broad normalization. The actual split, remnant insertion
and original native return compose with exact counter and selected frame
facts. Complete pick/pop/split composition is checked as `78081098`:
1,282 jobs, 199 allowed-axiom reports and 2 axiom-free declarations.
Original-memory list/header/map facts supply each intermediate input;
bitmap search before this route is now checked in `4eec805d`.
Final allocator preservation and other size classes remain open. Task rules now require the
build guard to stop failed or 10 GiB builds before the worker cap.

The first-insertion summary executes the actual prefix, `stat_checked` call,
24-byte cell/header stores and ABI return. It exports seed 25173, a level-0
chain, allocator readiness, selected owned-block frame and the domain key
at the generated backtrace offset. Full `Skiplist.Ops`, arbitrary insertion,
`RootsAt` and reset/backtrace caller composition remain open.

The attempted direct copy-string splice was refuted by the pinned target:
the short formatter calls `caml_alloc_initialized_string` at `0x8000c284`,
with length and source arguments. The real fit/argument/JAL continuation
passes 1,076 build jobs and 9 focused reports. The initialized-string callee
and its direct short formatter splice are now checked and reviewed as
`1150a772`: 1,403 affected jobs, 81 allowed-axiom reports and all focused
generator/discipline checks pass. It landed at `88d4c057`; no full formatter return is claimed.

The formatter summary executes native `vsnprintf` for plain `%ld`, including
truncation, NUL, length, saved registers and memory frame. Its ownership ends
before the real caller's parsed-format buffer (`snpAbove = 192`); a concrete
native entry proves the contract is satisfiable. Reachable caller suppliers,
string allocation, general `d/i/u/x/X/o` flags/width/precision, major allocation
and the C_CALL2 return remain open. Decimal-only progress does not close F1.

## Remaining F1 boundaries

All opcode row families and interpreter entry/halt composition are present;
`ocamlrun_refinement_F1_open` still consumes primitive/growth premises.
The five ordinary open C_CALL fields are the two descriptor opens, out-channel
listing, named registration, and integer formatting. Counted channel helpers
still need the remaining ordinary loop frames and actual runtime entry/after
suppliers. Concrete startup table occupancy, actual interpreter entry, shared
placement coherence and memory-preserving row reuse are checked; occupancy
alone does not supply the full custom-runtime predicate. CONST0/NEGINT are
the first checked ordinary counted rows, not a complete F1 table. `LibHeapAt.named` now carries ownership in the
selected ledger; named resource reserves and registration remain open. Distinct-key
provenance bounds nodes but does not account for repeated skiplist cell
allocation on root-class changes; actual removal/reuse remains required.

Reset-through-atoms is landed (`9c443c79`, audited at `bb55a4e5`); full
reset-to-cut/Loaded remains open. The captured allocator is checked as
`d959451a`: all 30 chunks, 127 bins and 27 live blocks, 16 MiB of credits,
3,211 affected build jobs and 577 allowed/axiom-free declaration audits.
The closed covers theorem supplies `libHeap`; `d890bf6a` removes its
obsolete generated caller argument, checked with 3,243 build jobs. This
reviewed fourth batch awaits full integration with the counted continuation. A captured loaded memory snapshot
is not reset execution. G2 pick/pop landed (`6d002aa5`); split/remnant is checked for the
next landing batch, including its complete pick/pop/split route. Bitmap
dispatch into fallback, final allocator preservation and full collection
remain open; the nonzero bitmap search is checked in `4eec805d`. The a2-sem uncaught-path
WIP is preserved and lower priority because GoodF1 excludes that path.

Queued work: remaining counted frames/table assembly and full physical
Customs supplier, full decimal formatter wrapper, general formatting, and
a proved named-node/key reserve plus repeated root-cell reuse accounting.
The captured allocator certificate is complete; reset/backtrace is active. See `tasks/sol-*.md`.
