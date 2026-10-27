# Foreman status

Updated 2026-10-27 21:47 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

Published `origin/main` is `333e9614`. The insertion/formatter batch passed
6,049 build jobs, 8,510 allowed-axiom reports, all generator/ELF checks,
and 329 OS traces (zero rejected). It includes the complete first empty
skiplist insertion, native `%ld` vsnprintf wrapper, concrete caller witness
and actual short formatter continuation to initialized-string entry.

The preceding counted-channel return bundle landed at `71547e46` with
6,038 jobs and 8,476 theorem reports. Physical named ownership landed at
`7e7a052a`; both passed the same full gate.

The next reviewed batch in `syo-wt/bprime` contains initialized-string
allocation (`1150a772`), G2 split/remnant return (`ecca3e24`), and the complete
pick/pop/split route (`78081098`). Its full gate is running after a coherent
cache handoff from the fully checked insertion worktree.
Local main contains these reviewed results; they are not yet published.
Prior WIP and reviewed tips remain preserved on `keep/*` branches.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| G2 Sol | Compose bitmap search with the checked pick/pop/split route | `syo-wt/a6-gc-next2` |
| Counted-loop Sol | Carry actual channel/custom counts through entry and the ordinary F1 loop | `syo-wt/a1-prims-next` |
| Lead | Initialized-string/G2 integration; captured allocator consumer check | main; `syo-wt/bprime`, `syo-wt/a0-boot-next` |

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
bitmap search before this route and final allocator preservation remain open. Task rules now require the
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
generator/discipline checks pass. It awaits the next integration batch in
`bprime`; no full formatter return is claimed.

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
still need ordinary loop preservation, startup physical zero and actual
runtime entry/after suppliers. `LibHeapAt.named` now carries ownership in the
selected ledger; named resource reserves and registration remain open. Distinct-key
provenance bounds nodes but does not account for repeated skiplist cell
allocation on root-class changes; actual removal/reuse remains required.

Reset-through-atoms is landed (`9c443c79`, audited at `bb55a4e5`); full
reset-to-cut/Loaded remains open. The captured allocator is checked as
`956ba74e`: all 30 chunks, 127 bins and 27 live blocks, 16 MiB of credits,
3,211 affected build jobs and 577 allowed/axiom-free declaration audits.
The closed covers theorem supplies `libHeap`; the lead is checking removal
of its obsolete generated caller argument before staging integration. A captured loaded memory snapshot
is not reset execution. G2 pick/pop landed (`6d002aa5`); split/remnant is checked for the
next landing batch, including its complete pick/pop/split route. Bitmap
search composition, allocator readiness and full collection remain open. The a2-sem uncaught-path
WIP is preserved and lower priority because GoodF1 excludes that path.

Queued tasks: ordinary counted-loop migration, actual startup/backtrace
composition after first insertion, a checked allocator-readiness certificate at the captured cut, and a proved
named-key reserve without adding the absent max-name/count guards. See `tasks/sol-*.md`.
