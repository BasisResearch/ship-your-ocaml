# Foreman status

Updated 2026-10-28 17:47 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently.

## Standing decisions

- `BarrierGrowthFull` remains G2; `CustomMemCall` remains a named premise.
- C4 abstraction-discovery round 2 waits until F1 closes.
- Separate Sol CLI workers, high reasoning, at most two. Each worker/build
  scope is capped at 12 GB; check 25 GB available before launch. Use the guard.
- Lead reviews, commits and lands through `scripts/integrate.sh`, with normal
  pushes to `origin/main`. Preserve reviewed snapshots on `keep/*` branches.
- Read `docs/lanes/DEAD-ENDS.md` before assigning a route again.

## Published

`origin/main` is **`29994e71e449eb89c336180dc4e82adc0357e3ec`**, verified remotely
after the full gate passed. It passed **6,208 build jobs**, **9,736 main
allowed-axiom reports** (9,740 including TCB), 150 axiom-free reports in the
gate transcript, generator/ELF checks and **329 OS traces** (5,069 steps,
324 accepted, 5 special, zero rejected or unsupported). All build dependency
reports also use only allowed axioms. Evidence:
`logs/{integrate,build}-29994e71.log`, `logs/gate-29994e71.json`.
The whole build reports 12,196 allowed-axiom dependencies, including the
imported G2 and CODE-entry audit modules. Exact totals are in the gate JSON.

The preceding `34658c24` batch published:

- `319f74d2`: four counted console returns and complete C_CALL4. The actual
  native windows preserve physical counts and per-record refs/links while
  buffers and offsets change; returned placement comes from native return
  evidence. The complete counted census is now **132/134**, with C_CALL1/2
  remaining. Lead checked all 36 new unique registrations, 2,372/3,713-job
  builds and 47 focused reports (46 standard, one pure).
  Snapshot: `keep/counted-console-reviewed-20261028`; `logs/console-counts-*`.
- `e99a7397`: original-entry exact/next-size small-success dispatch for
  positive requests <=16 with a suitable represented small list. Actual
  returns retain SmallRepresentation, physical separation, header, ABI and
  exact effects; natural counter credit remains explicit. Lead checked all
  27 new registrations, 1,291-job build and 287 focused reports (285
  standard, two pure). Snapshot: `keep/g2-exact-small-reviewed-20261028`;
  `logs/a6-exact-entry-*`. Remaining large cases/caller production are open.

The preceding `004b521c` published reset through interpreter/debugger to
`0x80004e94` and complete C_CALL3/5; its 6,141-job gate passed. It preserves
actual reset/descriptor/fd/argv ancestry, native steps and runtime/heap frames;
CODE/PRIM/DATA loading and Loaded are still open. Proof snapshots and
`logs/{interpreter-init,ccall35}-*` remain archived.

Earlier gates `51c9653c`, `dfbaf165` and `804538a5` published ordinary counted
primitive returns, selected custom ownership/spatial and barrier frames,
initial G2 next-size dispatch and plain decimal formatting. Their raw gate
and focused logs remain archived. `7047b3cd` isolates fd-2 seek probes so
validation cannot overwrite integration log headers; later full gates pass.

## Newly published counter and exit proofs

`9b490e19` supplies original-entry counted fresh-OO-ID success and actual
native C_CALL1 halt. The counter frame uses the selected heap and physical
counts; halt projects the counted relation and reuses pinned native exit.
Whole C_CALL1 still needs complete unary success coverage. Lead checked
all nine new unique registrations, 3,291/3,715-job builds and 77 focused
reports (75 standard, two pure). Rebase was clean.
Snapshot: `keep/counted-counter-exit-reviewed-20261028`;
evidence: `logs/counted-fresh-exit-*`. Published in `7ee29262`.

## Newly published listing repair and bitmap obstruction

`eddfc88c` checks the unused-high-bit obstruction in the existing small
representation and factors the actual missing-slot supplier. This is an
interface counterexample, not a reachable native state. Lead checked all
eight new unique registrations, 1,300/1,301-job builds and 295 focused
reports (293 standard, two pure). Snapshot:
`keep/g2-bitmap-obstruction-reviewed-20261028`; `logs/a6-entry-large-*`.
The repair below supersedes the failed derivation while retaining this
old-interface counterexample.

`e9b985ce` repairs listing entry to consume actual setup/stack evidence and
reconstructs returned heap/runtime fields, leaving numeric reserve on the
same returned ledger explicit. It adds the generated 792576-byte request,
1 MiB credit, snapshot credit producer, framing/composition and checked old
interface obstructions. Lead reviewed all 105 public theorems (plus generated
segments), all 117 focused reports (100 standard, 17 pure) and the 3,594-job
consumer build. Snapshot: `keep/outlist-runtime-reviewed-20261028`;
`logs/outlist-*`. Rebase retained both additive audit/lane/dead-end sections.
It does not close the native spending or full runtime supplier.

Both are published in `4e99ba14`; log `/tmp/syo-listing-bitmap-integrate.log`.

## Newly published bounded bitmap and least-large return

`d90918a9` repairs bitmap boundedness and supplies the original-entry
least-large split for positive requests<=16 and request+17<source size.
It derives actual filtering/setup, returns unchanged bounded small lists,
shortened source/header and allocated separation, exact counter/effects,
RA/SP and native frames. General tree topology, allocated colors, larger
requests, wrapper/caller production and natural total-free credit remain
open. Lead checked all 56 new registrations, 1,337-job final build and
352 focused reports (350 standard, two pure). Rebase was clean.
Snapshot: `keep/g2-bounded-large-reviewed-20261028`;
evidence: `logs/a6-bounded-*`. Published in `a017d2ba` after the full gate passed at 17:23 UTC;
log `/tmp/syo-bounded-large-integrate.log`.

## Newly published CODE seek entry

The startup prefix now reaches the actual optional-section entry at
`0x80004bcc`, with RA `0x80004ea8`, current trailer count/pointer and selected
descriptor ownership. The missing-section test is checked separately; the
reverse scan has not executed. Review checked all 247 new public theorem
registrations, 3,533 build jobs, 1,702 unique allowed-axiom and seven pure
reports. Focused audit registrations overlap intentionally.
Snapshot: `keep/startup-code-seek-entry-reviewed-20261028`;
evidence: `logs/code-seek-*`. The next packet repairs selected descriptor,
OpenFile/source-image and fd-position frames through actual initialization.

The CODE entry gate passed and published `29994e71` at 17:47 UTC;
log `/tmp/syo-code-seek-entry-integrate.log`.

## Reviewed physical custom state and call context

`53e93d16` supplies full mutable physical observations, separate native
read-only pins and their actual startup/caller frames. Physical footprint,
separation, accounting and readiness frame laws are concrete. The captured
entry reaches the counted loop without a custom-call premise at startup.
Later native execution, floating-point linkage and spending remain within
named `CustomMemCall`. Lead checked all 45 new unique registrations, the
3,679-job final consumer build and all 62 focused reports (59 allowed-axiom,
three pure). Source parameter arithmetic was also checked against custom.c.
Only additive lane/dead-end sections conflicted on rebase; both were kept.
Snapshot: `keep/custom-physical-reviewed-20261028`;
evidence: `logs/custom-physical-*`. The physical-state gate follows in bprime, started 17:48 UTC; log
`/tmp/syo-custom-physical-integrate.log`. No active worker cache is copied.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Startup Sol | Current descriptor/file/source frames at actual CODE seek entry | `syo-wt/a6-gc-next2` |
| Runtime Sol | Selected native custom credit through listing runtime | `syo-wt/a1-prims-next` |
| Lead | Gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

Startup entry handoff from 17:10 UTC is reviewed. Next packet:
`tasks/sol-startup-seek-frames.md`, log `/tmp/syo-startup-seek-frames-launch.log`.
Its actual descriptor/file source must be framed through the executed
initialization, not assumed at the new PC.
G2's next rotation packet is `tasks/sol-g2-large-wrapper.md`: original-caller
wrapper conditions and returned representation/color for the reviewed branch.
Its other branch/caller work stays in the ledger.
Physical custom work is reviewed. Its slot now takes
`tasks/sol-custom-credit-listing.md`, log
`/tmp/syo-custom-credit-listing-launch.log`, to carry actual selected input
credit and native returned spending through the listing walk. The physical
worker cache is retained in that slot; no cache is copied while bprime builds.

## Remaining F1 boundaries

The published **132/134** table is relative to named `CustomMemCall` and
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`.
The base-layout G2 contract cannot supply the extra returned counts.

C_CALL1 needs concrete opening/listing runtime producers and composition of
all unary successes; reviewed counter and exit cover those branches.
C_CALL2 needs named registration and general formatting. Named registration
must derive node/key reserve from immutable source provenance, including
fully initialized partialBytes, and account separately for repeated root-cell
removal/reallocation. Fixed name/count guards are absent from GoodF1.
Formatting still needs full grammar/printf conversions, flags/width/precision,
large-result allocation and actual caller/runtime suppliers. Major-heap
expansion must generalize the fixed free-list, heap-size pin and resource
target specialization; it cannot preserve those captured constants by fiat.

Custom allocation needs concrete input credit and returned spending on the
same selected heap; an existential HeapReady capacity alone supplies neither.
Reviewed PhysicalCustoms now has table-shape/startup/read-context producers
and an actual captured counted entry. Captured memory is still not reset
execution, and arbitrary Loaded alone supplies no initial physical witness.

Reset-to-Loaded still needs CODE/PRIM/DATA loading, promotion and system/argv.
The next actual native call is caml_seek_optional_section; retained ancestor
Steps alone do not frame its descriptor/file memory into the current state.
Ready packets cover this seek, opening runtime, physical custom state, general
format parsing and named reserve. G2 also needs remaining tree/size/color
cases, caller invariant production, full allocator readiness and collection.
No user-only decision currently blocks work.
