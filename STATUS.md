# Foreman status

Updated 2026-10-28 15:43 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

`origin/main` is **`dfbaf16567d49618803d7cd6be32c4e51bfb3c20`**, independently
verified remotely after the full gate exited successfully at 15:39 UTC.
The gate passed **6,095 build jobs**, **9,542 main axiom reports**, generated
and ELF checks, and **329 OS traces** (5,069 steps, 324 accepted, 5 special,
zero rejected or unsupported). C4 remains below its discovery threshold.

This batch contains:

- `9de2d983`: 122 counted opcode rows, with actual native/count frames.
- `2e47e2fc`: local custom-space repair, selected ownership and physical
  allocation footprint; removes the old universal record-separation law.
- `9549edb8`: field and empty-growth frames.
- `4f827ee5`: actual insertion separation from `LibHeapAt.refCustomApart`,
  completing all seven field rows and the **129/134** counted table.
- `d1314b91`: original best-fit entry through next-size allocation and return,
  retaining SmallRepresentation and actual allocated-block separation.

Evidence: `logs/integrate-dfbaf165.log`, `logs/build-dfbaf165.log`,
`logs/integrate-dfbaf165-notes.txt`, and `logs/{counted-spatial,a6-entry-next}-*`.
The OS driver's inherited fd 2 seek overwrote the start of the raw gate log;
its exit, final success, full build and remote push were verified separately.
The raw archive is preserved. `7047b3cd` isolates driver stderr; a capped
329-trace check retained leading/trailing log markers. That fix is reviewed
for the next gate, not yet published.

Previous published `804538a5` includes `da1ab268` (plain signed decimal native
entry-to-return) and `58740097` (selected custom ownership/ledger). Their
6,090-job full gate and review evidence remain in `logs/*804538a5*`,
`logs/counted-prim-*` and the lane logs. General formatting remains open.

## Reviewed for the next gate

`19b964fd` supplies original-entry counted C_CALL1/2 success for 19 ordinary
primitive names (16 unary, three binary), reusing actual native returns.
The original count witness comes from the counted loop and returned counts
use the actual placement. Existing channel consumers still check.
Its 3,698-job downstream build and 63 focused reports passed; lead checked
all 52 new registrations and allowed axioms. Evidence: `logs/counted-prim-*`;
preserved snapshot: `keep/counted-ordinary-reviewed-20261028`.
Whole C_CALL rows remain open. The next full gate will include this result,
the validation-log fix and the current task/status packets.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| C_CALL Sol | Complete C_CALL3/5 from checked F1 arity classification | `syo-wt/a6-gc-next2` |
| Startup Sol | Universal reset through null-interpreter/debugger initialization | `syo-wt/a1-prims-next` |
| Lead | Next full gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

C_CALL3/5 source review covers all primitive outcomes and malformed operands;
its shared helper now builds, and downstream table checks are running. The
proposed **131/134** census is not yet a reviewed/published result.
Startup is repairing a default-budget kernel recursion failure in the new
save-bank proof; no budget increase or reset-to-Loaded claim is authorized.

G2's next-size entry result has landed. `sol-gc-small-success.md` is the next
G2 rotation: exact-size representation and shared original small dispatch.
Other ready packets: counted console/C_CALL4, counted counter/exit, listing
runtime repair, full physical custom startup/read context, general format
parser, named reserve, and the actual startup CODE-section seek.

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

Reset needs the continuation after backtrace through interpreter/debugger,
CODE/primitive/DATA loading, promotion, system/argv setup and `Loaded`.
The next ELF call after debugger initialization is directly to
`caml_seek_optional_section`, not a separate seek wrapper. Its input must
frame the retained executed descriptor/file history, not assume a snapshot.
G2 still needs original invariant production, remaining size classes/colors,
complete allocator readiness and collection. The uncaught-path WIP stays
preserved at lower priority because GoodF1 excludes that path.

No user-only decision currently blocks work.
