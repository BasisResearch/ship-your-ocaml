# Foreman status

Updated 2026-10-28 16:38 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains G2; `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes.
- Separate Sol CLI workers, high reasoning, at most two. Each worker/build
  scope is capped at 12 GB; check 25 GB available before launch. Use the guard.
- Lead reviews, commits, and lands through `scripts/integrate.sh`, with normal
  pushes to `origin/main`. Preserve reviewed snapshots on `keep/*` branches.
- Read `docs/lanes/DEAD-ENDS.md` before assigning a route again.

## Published

`origin/main` is **`004b521cc338bcf6d93fbaf13b265e3644f7d3c2`**, verified remotely
after the full gate exited at 16:34 UTC. It passed **6,141 build jobs**,
**9,598 main audit reports** (9,602 including TCB) and 133 axiom-free reports
in the gate transcript, generator/ELF checks, and **329 OS traces** (5,069
steps, 324 accepted, 5 special, zero rejected or unsupported). All stages
passed. Evidence: `logs/{integrate,build}-004b521c.log`.
This publishes the reset-through-debugger and complete C_CALL3/5 work below.
The counted published census is **131/134**. All build-log dependency reports,
including focused audits replayed during builds, also use only allowed axioms.

The previous `51c9653c` gate passed 6,098 jobs, 9,596 allowed reports including
TCB, 133 pure reports and the same 329 traces; evidence remains archived.
This adds `19b964fd`: original-entry counted C_CALL1/2 success for **19 ordinary
primitive names** (16 unary, three binary), using actual native returns.
Entry counts come from the counted loop, and returned counts use the actual
returned placement. Lead checked all 52 new registrations, the 3,698-job
downstream build and 63 focused reports before integration.
`keep/counted-ordinary-reviewed-20261028` preserves its reviewed snapshot.

The previous `dfbaf165` batch published `9de2d983` (122 counted rows),
`2e47e2fc` (selected custom-space repair), `9549edb8` (field/empty-growth
frames), `4f827ee5` (actual insertion separation and **129/134** table), and
`d1314b91` (original best-fit entry through next-size allocation return,
with SmallRepresentation and actual allocated separation).
Its 6,095-job gate passed 9,546 allowed reports and 131 axiom-free reports.
Evidence: `logs/*dfbaf165*`, `logs/{counted-spatial,a6-entry-next}-*`.

`7047b3cd` fixes inherited stderr offset corruption by the OS driver's fd 2
seek probe. The old raw gate log and explanatory notes are preserved; its
axiom reports survived, but its initial stage headers were overwritten.
A capped targeted check and the subsequent full gate verify the fix.

Earlier published `804538a5` contains the plain signed decimal native wrapper
and selected custom ownership. General formatting remains open.

## Newly published proofs

`66a597af` executes universal parsed-ELF reset through interpreter/debugger
initialization to `0x80004e94`. It retains the actual backtrace/descriptor
ancestry, local Steps, fd/argv bank, thirteen saves, restored ABI, runtime/
capacity, owned heap/caller frames, page table and tagged-unit root.
Its 3,481-job affected build passed. Lead independently checked all 99 new
public registrations, all 117 initialization and 80 backtrace audit reports
(only standard axioms or no axioms), and the actual native composition.
The sole rebase conflict was adjacent dead-end notes; both were retained.
Snapshot: `keep/interpreter-init-reviewed-20261028`; evidence:
`logs/interpreter-init-*`. `10c5e3c6` removes the duplicate GC-call witness
from the generated backtrace audit (now 79 declarations); initialization
still audits it. The full gate checked the combined result.

`607536da` closes C_CALL3/5, with a reviewed **131/134** census. The worker's
3,184-job table build and 12 focused reports (11 standard, one axiom-free)
passed; all six new declarations have unique audit registrations. The actual
absent-slot branch remains `.wrong`; selected F1 primitives at these arities
are `.unsupported`. Neither can occur on a GoodF1 run. No guard changed.
Snapshot: `keep/counted-arity-reviewed-20261028`; logs: `logs/ccall35-*`.
`b83bf39e` moves the two proof bodies unchanged to `Bytecode/PrimArity.lean`;
Semantics.lean is byte-identical to the preceding published baseline. The full
gate validated the import change and combined 131-row/startup result.

Both proof batches landed through `scripts/integrate.sh`; worker logs now
end with the actual landed commit. The review snapshots remain preserved.

## Reviewed for the next gate

`e99a7397` completes original-entry exact/next-size small-success dispatch for
positive requests <=16 when a suitable represented small list exists.
All four exact branches reuse the actual native run and return the popped
SmallRepresentation, original header/size, allocated separation, ABI/stack,
code/output and exact log. Shared dispatch selects the real branch; no
intermediate or final state is assumed. Natural counter credit remains an
explicit separate duty. Lead checked the 1,291-job build, all 287 focused
reports (285 standard, two pure) and all 27 new unique registrations.
Snapshot: `keep/g2-exact-small-reviewed-20261028`; logs: `logs/a6-exact-entry-*`.
The proof rebase was clean. This result is not yet published.

`319f74d2` closes complete C_CALL4 and the four counted console returns,
bringing the generated table to **132/134**. C_CALL1/2 remain. Lead reviewed
actual ref/link/physical-count frames and every arity-four outcome, checked
all 36 new unique registrations, the 2,372/3,713-job affected builds and
47 focused reports (46 standard, one axiom-free). All 131 prior complete row
terms remain unchanged. Snapshot: `keep/counted-console-reviewed-20261028`;
evidence: `logs/console-counts-*`. Rebase conflicts were adjacent lane and
dead-end notes; both sides were retained. It is not yet published.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| C_CALL Sol | Counted fresh-OO-ID success and actual sys_exit halt | `syo-wt/a6-gc-next2` |
| Runtime Sol | Listing entry/runtime contract and concrete custom allocation credit | `syo-wt/a1-prims-next` |
| Lead | Next full gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

Counter/exit started at 16:35 UTC from `319f74d2`; log:
`/tmp/syo-counted-counter-exit-launch.log`. Listing started at 16:15 UTC from
`a1be6936`; log: `/tmp/syo-outlist-runtime-local-launch.log`.
G2's exact/next-size task is reviewed for the next gate; the original-entry
least-large split/return packet is ready for its next rotation. Other ready
packets cover physical custom startup/read context, general formatting,
named reserve and actual CODE-section seek. No worker cache is copied while
that worktree is building.

## Remaining F1 boundaries

The published counted table supplies **131/134** rows relative to named
`CustomMemCall` and counted full growth. The G2 boundary is genuinely
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`;
a base-layout boundary cannot supply the extra returned count facts.

C_CALL1/2/4 remain whole-row obligations in the published table; reviewed
C_CALL4 will reduce that to C_CALL1/2 at the next gate. Opening and
listing have native returns, but concrete entry/runtime suppliers remain.
Inspection found that `OutListRuntime.entry` quantifies over an unconstrained
stack pointer and its return law permits arbitrary allocator writes. The
queued repair must use the actual setup and returned selected heap. This is
not yet a checked obstruction or a reachable counterexample.
`CustomMemReturned.heap` alone gives no returned-capacity spending bound;
future C-allocation reserves need a concrete native charge/credit contract.

Physical Customs needs actual startup and call-read-context producers, not
just occupancy or the abstract refcount sum. Captured-memory count producers
are not reset execution. `counted_entry_of_custom` explicitly needs an
initial physical-count witness; existing `Loaded` alone does not supply it.
Do not silently drop that boundary in final theorem assembly.

Named registration needs node/key reserve and repeated root-cell removal/
reuse accounting. Distinct names alone do not bound all allocation calls.
Formatting needs general d/i/u/x/X/o flags/width/precision, large/major
allocation, actual caller/runtime suppliers and its C_CALL2 return.

The reviewed reset prefix reaches the debugger return. Reset-to-Loaded still
needs CODE/primitive/DATA loading, promotion, system/argv and representation.
The next ELF call after debugger initialization is directly to
`caml_seek_optional_section`, not a separate seek wrapper. Its input must
frame the retained executed descriptor/file history, not assume a snapshot.
G2 still needs original invariant production, remaining size classes/colors,
complete allocator readiness and collection. The uncaught-path WIP stays
preserved at lower priority because GoodF1 excludes that path.

No user-only decision currently blocks work.
