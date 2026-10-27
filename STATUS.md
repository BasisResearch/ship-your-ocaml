# Foreman status

Updated 2026-10-27 21:18 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

Published `origin/main` is `71547e46`. The physical named-table migration
landed at `7e7a052a`: 6,033 build jobs, 8,424 theorem audits, all generator/ELF
checks and 329 OS traces (zero rejected). The next two batches are:

1. Complete counted channel returns, `71547e46`, in `syo-wt/a1-prims-next`.
   Landed through the full gate: 6,038 build jobs, 8,476 theorem audits,
   all generators/ELF checks and 329 OS traces (zero rejected). The final worker check passed
   3,687 build jobs and 31 focused axiom reports; earlier count/setup
   checkpoints passed 52 and 27 reports. Actual `CustomMemCall` posts carry
   the count increment; native refcount stores/no-wrap facts reconstruct
   complete channel counts at the same returned placement. The unary arm
   retains that placement through its suffix.
2. First empty-skiplist insertion plus native decimal formatter, `8b1f1377`,
   staged in `syo-wt/a6-gc` on top of the landed channel bundle. Both workers
   finished and the lead reviewed/committed their results. First insertion
   passes 2,720 jobs, 310 standard-axiom audits and startup generator drift.
   The `%ld` wrapper passes 978 jobs, its concrete caller check, 34 focused
   reports, stdio generator drift, hole/discipline/abstraction gates.
   The batch also includes the checked short formatter continuation. Its
   full integration is running after a coherent cache handoff.

Local `main` includes the second reviewed batch to support subsequent worker
work; that batch has not yet passed the full gate or reached origin.
The earlier worker WIP and reviewed tips are preserved on `keep/*` branches.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| G2 Sol | Compose the complete next-size pick/pop/split native return | `syo-wt/a6-gc-next2` |
| Counted-loop Sol | Carry actual channel/custom counts through entry and the ordinary F1 loop | `syo-wt/a1-prims-next` |
| Lead | Insertion/formatter gate; initialized-string and G2 split landing batch | main; `syo-wt/a6-gc`, `syo-wt/bprime` |

The first G2 split attempt reached the 12 GB cgroup cap while building
`BestFitNext`, after its generated split module passed 609 jobs. WIP is
preserved (`keep/gc-split-20261027-2057`), and the resumed worker isolated
the expensive declarations under a 6 GB diagnostic limit. The checked result
`ecca3e24` passes 1,264 affected jobs and 180 standard-axiom reports, with
generator and discipline checks. Bounded scalar/log/access certificates
replace the failed broad normalization. The actual split, remnant insertion
and original native return compose with exact counter and selected frame
facts; complete entry-to-return pick/pop/split composition is next. Task rules now require the
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
selected ledger; named resource reserves and registration remain open.

Reset-through-atoms is landed (`9c443c79`, audited at `bb55a4e5`), but full
reset-to-cut/Loaded and `libHeap` are open. A captured loaded memory snapshot
is not reset execution. G2 pick/pop landed (`6d002aa5`); split/remnant is checked for the
next landing batch; whole-route composition, allocator readiness and full
collection remain open. The a2-sem uncaught-path
WIP is preserved and lower priority because GoodF1 excludes that path.

Queued tasks: ordinary counted-loop migration, actual startup/backtrace
composition after first insertion, a checked allocator-readiness certificate at the captured cut, and a proved
named-key reserve without adding the absent max-name/count guards. See `tasks/sol-*.md`.
