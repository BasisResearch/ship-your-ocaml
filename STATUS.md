# Foreman status

Updated 2026-10-28 18:43 UTC. Target: Layer A for `GoodF1`, with G2 continuing.

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

## Reviewed concrete listing runtime

The selected-credit continuation now supplies `f1_outList_runtime` relative
only to named `CustomMemCall`. Actual startup/ordinary frames retain the
extra custom reserve; each native call returns spending on one selected
heap/capacity. Listing retains that credit through its real walk and return,
and the counted listing adapter no longer takes a separate runtime supplier.
Opening's spatial return retains the same spending evidence for its next
runtime task. Lead checked six new unique registrations, the 3,682-job final
build and all 144 focused reports (126 allowed-axiom, 18 pure). Rebase clean.
Snapshot: `keep/custom-credit-listing-reviewed-20261028`;
evidence: `logs/custom-credit-*`. This follows the active physical-state gate.

## Reviewed current CODE source frames

`2165d4de` closes current descriptor/file/source observations at the actual
optional-section entry. Selected descriptor/name LiveFrames and actual
fresh page-table provenance compose through initialization; HTIF and
scratch-bounded image frames supply current file size, fd position and
all descriptor bytes. The universal reset producer has no later-memory
matching premise. Lead checked 37 new public registrations, the 3,533-job
build and exact 37 focused reports (36 allowed-axiom, one pure).
Snapshot: `keep/startup-code-source-reviewed-20261028`;
evidence: `logs/code-source-*`. Only additive dead-end notes conflicted;
both were retained. This is queued behind the active physical-state gate.
The native reverse scan and lseek remain open.

## Reviewed concrete opening runtime

`9f4e4fa1` supplies `f1_openOut_runtime` relative only to named CustomMemCall.
Its actual caller supplies OutInput/OutNursery and the selected list bound;
its native return supplies one credited ledger, the fresh record, framed
remembered-table words and named/custom separation. Core transfer excludes
the changed channel-list head while retaining the ordinary footprint API.
Both counted opening adapters and the three-channel dispatcher now consume
the concrete producer. Lead reviewed nine unique new registrations, all
3,683 consumer build jobs and exact 161 focused reports (141 allowed-axiom,
20 pure). Only additive dead-end notes conflicted on rebase; both retained.
Snapshot: `keep/opening-runtime-reviewed-20261028`;
evidence: `logs/opening-runtime-*`. This joins the next integration batch.
Whole unary opcode assembly remains open until its own proof checks.

## Reviewed original-caller bounded G2 wrapper

`ce120d18` composes the real allocator wrapper, bounded least-large split,
phase-selected header/color, accounting and original caller restoration.
Original inputs derive the internal conditions and returned bounded small
representation, shortened source, separation, exact counters and write log.
Geometry is kept distinct from ownership; natural credit and no-major-slice
conditions remain explicit original-state requirements. Shared LogWindows
and selected LiveFrame adapters use the actual composed log.
Lead checked all 39 new unique registrations, 1,419 affected build jobs and
43 exact focused reports (40 allowed-axiom, three pure). Only additive a6
lane notes conflicted on rebase; both were retained.
Snapshot: `keep/g2-large-wrapper-reviewed-20261028`;
evidence: `logs/a6-wrapper-*`. General caller production, small wrappers,
requests>16, arbitrary trees, expansion and collection remain open.

## Active work

| Slot | Target | Worktree |
| --- | --- | --- |
| Startup Sol | Actual CODE reverse scan, lseek and return | `syo-wt/a6-gc-next2` |
| Unary Sol | Complete counted C_CALL1 opcode and census assembly | `syo-wt/a1-prims-next` |
| Lead | Gate, result review and concrete runtime supplier analysis | main; `syo-wt/bprime` |

The bounded G2 wrapper is reviewed and committed. That slot returns to
`tasks/sol-code-seek-scan.md`, log `/tmp/syo-code-seek-scan-launch.log`.
The next G2 rotation is `tasks/sol-g2-small-wrapper.md`, reusing shared
original-caller frame suppliers for exact/next-size small success.
Opening and listing runtime producers are reviewed. That slot now takes
`tasks/sol-counted-unary-complete.md`, log
`/tmp/syo-counted-unary-complete-launch.log`. No active worker cache is
copied into bprime.
After checked unary assembly, the primitive slot takes
`tasks/sol-format-parse-all.md` for the complete native parser/caller prefix;
named storage and root-cell resource work stays in `tasks/sol-named-reserve.md`.
These rotations keep both F1 and G2 moving; remaining caller and native
execution boundaries stay explicit.

## Remaining F1 boundaries

The published **132/134** table is relative to named `CustomMemCall` and
`∀ cp world, BarrierGrowthFull (countedLayout f1Layout Customs cp world)`.
The base-layout G2 contract cannot supply the extra returned counts.

C_CALL1 needs composition of all unary successes and actual exit. Opening
and listing runtime producers are reviewed; counter and exit are checked.
Its active assembly packet is tasks/sol-counted-unary-complete.md.
C_CALL2 needs named registration and general formatting. Named registration
must derive node/key reserve from immutable source provenance, including
fully initialized partialBytes, and account separately for repeated root-cell
removal/reallocation. Fixed name/count guards are absent from GoodF1.
Formatting still needs full grammar/printf conversions, flags/width/precision,
large-result allocation and actual caller/runtime suppliers. Major-heap
expansion must generalize the fixed free-list, heap-size pin and resource
target specialization; it cannot preserve those captured constants by fiat.

Reviewed custom input credit and returned spending now use the same selected
heap throughout listing; native execution/spending remain named duties.
Reviewed PhysicalCustoms now has table-shape/startup/read-context producers
and an actual captured counted entry. Captured memory is still not reset
execution, and arbitrary Loaded alone supplies no initial physical witness.

Reset-to-Loaded still needs CODE/PRIM/DATA loading, promotion and system/argv.
Current descriptor/file memory at caml_seek_optional_section now follows
from reviewed actual reset frames. The call still needs its native reverse
scan, lseek and return composition.
Ready packets cover this seek, opening runtime, physical custom state, general
format parsing and named reserve. G2 also needs remaining tree/size/color
cases, caller invariant production, full allocator readiness and collection.
No user-only decision currently blocks work.
