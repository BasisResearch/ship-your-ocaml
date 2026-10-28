# Foreman status

Updated 2026-10-28 15:59 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

`origin/main` is **`51c9653c02784a3b83742eb176524659305553ab`**, verified remotely
after the full gate exited at 15:49 UTC. It passed **6,098 build jobs**,
**9,592 main audit reports** (9,596 including TCB) and 133 axiom-free reports,
generator/ELF checks, and **329 OS traces** (5,069 steps, 324 accepted,
5 special, zero rejected or unsupported). Every stage marker and the complete
log header/tail are intact. Evidence: `logs/{integrate,build}-51c9653c.log`.

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

## Reviewed for the next gate

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
still audits it. The full gate will check the combined result.

C_CALL3/5 has passed its 3,184-job table build and 12 focused reports; six
new theorems have unique registrations. The worker is finishing its handoff,
so this **131/134** census is not yet reviewed or published. It closes those
whole rows from actual F1 arity rejection without changing GoodF1.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| C_CALL Sol | Complete C_CALL3/5 from checked F1 arity classification | `syo-wt/a6-gc-next2` |
| G2 Sol | Exact-size representation and shared original small-success dispatch | `syo-wt/a1-prims-next` |
| Lead | Next full gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

Two Sol CLI workers are active. G2 started at 15:58 UTC from `10c5e3c6`
in `a1-prims-next`; log `/tmp/syo-gc-small-success-launch.log`.
The idle startup cache was transferred to the integration worktree under
source/destination build locks, with matching toolchain/manifests and
tracked dependency trees, before the G2 launch. All four build roots were
copied coherently, without deletion.

The next call slot is counted console/C_CALL4. Other ready packets cover
counter/exit, listing runtime repair, full physical custom startup/read
context, general formatting, named reserve and the actual CODE-section seek.

## Remaining F1 boundaries

The published counted table supplies **129/134** rows relative to named
`CustomMemCall` and counted full growth. The G2 boundary is genuinely
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`;
a base-layout boundary cannot supply the extra returned count facts.

C_CALL1–5 remain whole-row obligations in the published table. Opening and
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
