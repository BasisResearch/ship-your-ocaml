# Foreman status

Updated 2026-10-28 20:04 UTC. Target: close Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently. Work continues; no user-only decision blocks the next steps.

## Current result

The published counted table is **133/134**: complete `C_CALL1` is checked
and integrated; `C_CALL2` remains. This does not establish reset-to-Loaded
or full G2.
Standing decisions: `BarrierGrowthFull` remains G2; `CustomMemCall` remains a
named premise; C4 abstraction-discovery round 2 waits until F1 closes.
GoodF1 has not been narrowed to simplify named registration or formatting.

## Published and landing

`origin/main`: **`92be3a3e9db89510c6ec67c19c44861a26cf57e4`**, independently
verified after the 20:02 UTC gate. It passed 6,217 jobs, 9,796 main
allowed-axiom reports (9,800 including TCB), 154 axiom-free reports in the
gate transcript and 329 OS traces: 5,069 steps, 324 accepted, five special,
zero rejected/unsupported. The whole build has 12,512 allowed-axiom reports.
Evidence: `logs/{integrate,build}-92be3a3e.log`, `logs/gate-92be3a3e.json`.

This publishes complete C_CALL1, concrete channel runtimes, current CODE
source frames and the bounded original G2 wrapper below. Physical custom
state/read context was published in `4c4209ea`; its gate evidence remains
archived alongside `logs/custom-physical-*`.

**CODE scan integration:** `d9c0be7b` plus handoff/status commits is the next
reviewed batch in bprime. Log: `/tmp/syo-code-scan-integrate.log`; bprime
`.integrate.log` and `.check-build.log`. The candidate is fixed at launch;
do not change that tree's HEAD, source or cache mid-gate.

All publication goes through `scripts/integrate.sh` and normal fast-forward
pushes to origin/main. Reviewed snapshots remain on `keep/*` branches.

## Recent proof handoffs

The first five commits below are published in `92be3a3e`; the final CODE
scan commit is queued for the next gate.

| Commit | Result | Lead-reviewed evidence |
| --- | --- | --- |
| `66343b8a` | Selected custom reserve/spending on one returned ledger; concrete listing runtime relative only to CustomMemCall | Six new registrations; 3,682 jobs; 144 focused (126 allowed, 18 pure); `logs/custom-credit-*` |
| `2165d4de` | Current CODE descriptor/file/image observations derived from actual reset initialization, without later-memory matching premises | 37 new registrations; 3,533 jobs; 37 focused (36 allowed, one pure); `logs/code-source-*` |
| `9f4e4fa1` | Concrete channel-opening runtime and counted in/out adapters, relative only to CustomMemCall | Nine new registrations; 3,683 jobs; 161 focused (141 allowed, 20 pure); `logs/opening-runtime-*` |
| `ce120d18` | Original-caller bounded least-large allocation wrapper, actual color/header, remaining representation, exact counters/log/ABI | 39 new registrations; 1,419 jobs; 43 focused (40 allowed, three pure); `logs/a6-wrapper-*` |
| `26201d6b` | Complete counted C_CALL1 using concrete ordinary/channel/counter/flush returns and actual native exit; table 133/134 | Four new registrations; 3,733 jobs; 22 focused (21 allowed, one pure); `logs/counted-unary-*` |
| `d9c0be7b` | Actual reset through reverse CODE scan, lseek and return at 0x80004eb0; length 764, fd position 57, selected ownership/runtime/source frames | 80 new registrations; 3,545 jobs; 80 focused (78 allowed, two pure); 2,157 generated outputs and ELF pins; `logs/code-scan-*` |

`d9c0be7b` is not in published `92be3a3e`.
The CODE worker was stopped after its checks and notes were complete and
it remained quiet with no active command. Reviewed source hashes were
unchanged; its task was preserved and committed. Only additive dead-end
notes conflicted on rebase, and both were retained.

Each focused list was checked exactly against its registrations and allowed
axioms. The CODE scan still requires its full integration gate. Rebase conflicts were
additive lane/dead-end notes and retained both sides. Snapshot branches:
`keep/custom-physical-reviewed-20261028`,
`keep/custom-credit-listing-reviewed-20261028`,
`keep/startup-code-source-reviewed-20261028`,
`keep/opening-runtime-reviewed-20261028`,
`keep/g2-large-wrapper-reviewed-20261028`,
`keep/counted-unary-reviewed-20261028`,
`keep/startup-code-scan-reviewed-20261028`.

## Active workers and next tasks

At most two separate **gpt-6.1-sol / high** CLI workers; no built-in proving
agents. `codexwork.sh` checks available memory and encloses each worker and
its builds in a 12 GB systemd scope. Builds use `lean-guarded.py` and
`lean-capped.sh`; one build per tree, at least 25 GB available before launch.
No active worker cache is copied into bprime.

| Slot | Current task | Log |
| --- | --- | --- |
| `syo-wt/a6-gc-next2` | Original-caller exact/next-size small G2 wrapper | `/tmp/syo-g2-small-wrapper-launch.log` |
| `syo-wt/a1-prims-next` | Full native format parser including l/n/L and actual signed/unsigned caller prefix to alloc_sprintf | `logs/sol-a1-prims-next-20261028-184554-2825386.log` |
| Lead | Gate, independent review, next-task contracts and integration | main and bprime |

The parser/caller modules and 52 focused reports pass. Its unchanged decimal
consumer hits the 10 GiB early guard; the worker is trying a single-thread
check under the same hard cap before claiming compatibility.
The CODE task is reviewed and committed. Current G2 task:
`tasks/sol-g2-small-wrapper.md`, then `tasks/sol-code-load.md` (actual CODE
allocation/read to code-fragment registration entry). Current primitive task:
`tasks/sol-format-parse-all.md`, then `tasks/sol-named-reserve.md` and
`tasks/sol-format-decoder.md`. Read `docs/lanes/DEAD-ENDS.md` before reassignment.
All task packets start with binding rules and stay under 40 lines.

## Remaining F1 and G2 boundaries

- **C_CALL2 / named registration:** derive node/key storage from immutable
  first-NUL byte-key provenance, including fully initialized partialBytes.
  maxNamed=16/maxNameLen=64 are absent from GoodF1. Repeated root-class
  changes also free/reallocate skiplist cells. The current allocator room
  counts space above top, not free bins; interior free does not supply a
  charge refund. Keep selected-ledger reserve and native root operations
  explicit until their producers are checked.
- **C_CALL2 / formatting:** full newlib integer decoding, conversions,
  flags/width/precision, result allocation and original caller/runtime return.
  The active parser/prefix task does not close these. Large results are
  allowed by Fits; major-heap expansion cannot preserve fixed initial
  free-list/heap-size/resource pins by fiat.
- **Initial relation:** the captured whileMin physical/counting entry is
  checked, but captured memory is not reset execution. Arbitrary Loaded
  does not imply an initial PhysicalCustoms witness.
- **Reset to Loaded:** CODE allocation/read,
  code fragments/digest, PRIM, DATA unmarshalling, promotion and system/argv.
  The complete CODE scan/lseek/return and its current source observations
  are reviewed in `d9c0be7b`.
- **G2:** small original wrappers, remaining tree/size cases, requests>16,
  heap expansion, caller invariant production, full allocator readiness and
  collection. The counted table requires returned custom-count preservation
  in `BarrierGrowthFull`; the base-layout contract alone cannot supply it.

Detailed completed work and residuals remain in PHASES.md and the lane logs;
older publication evidence remains in `logs/gate-*.json` and raw logs.
