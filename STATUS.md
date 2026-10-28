# Foreman status

Updated 2026-10-28 20:12 UTC. Target: close Layer A for `GoodF1`, with G2 continuing.

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

`origin/main`: **`91e7083b5842d2a4c9ffab601e1d2dd749e1f6a2`**, independently
verified after the 20:08 UTC gate. It passed 6,248 jobs, 9,796 main
allowed-axiom reports (9,800 including TCB), 154 axiom-free reports in the
gate transcript and 329 OS traces: 5,069 steps, 324 accepted, five special,
zero rejected/unsupported. The whole build has 12,595 allowed-axiom reports.
Evidence: `logs/{integrate,build}-91e7083b.log`, `logs/gate-91e7083b.json`.

This publishes the actual reset-through-CODE-scan result, following complete
C_CALL1, concrete channel runtimes, CODE source frames and the bounded G2
wrapper in `92be3a3e`. Physical custom state/read context was published in
`4c4209ea`; all preceding gate evidence remains archived.

No integration gate is currently running. The formatter is under final
lead validation; the next gate will be fixed at its reviewed candidate.

All publication goes through `scripts/integrate.sh` and normal fast-forward
pushes to origin/main. Reviewed snapshots remain on `keep/*` branches.

## Recent proof handoffs

All six commits below are published: the first five in `92be3a3e`,
and the final CODE scan in `91e7083b`.

| Commit | Result | Lead-reviewed evidence |
| --- | --- | --- |
| `66343b8a` | Selected custom reserve/spending on one returned ledger; concrete listing runtime relative only to CustomMemCall | Six new registrations; 3,682 jobs; 144 focused (126 allowed, 18 pure); `logs/custom-credit-*` |
| `2165d4de` | Current CODE descriptor/file/image observations derived from actual reset initialization, without later-memory matching premises | 37 new registrations; 3,533 jobs; 37 focused (36 allowed, one pure); `logs/code-source-*` |
| `9f4e4fa1` | Concrete channel-opening runtime and counted in/out adapters, relative only to CustomMemCall | Nine new registrations; 3,683 jobs; 161 focused (141 allowed, 20 pure); `logs/opening-runtime-*` |
| `ce120d18` | Original-caller bounded least-large allocation wrapper, actual color/header, remaining representation, exact counters/log/ABI | 39 new registrations; 1,419 jobs; 43 focused (40 allowed, three pure); `logs/a6-wrapper-*` |
| `26201d6b` | Complete counted C_CALL1 using concrete ordinary/channel/counter/flush returns and actual native exit; table 133/134 | Four new registrations; 3,733 jobs; 22 focused (21 allowed, one pure); `logs/counted-unary-*` |
| `d9c0be7b` | Actual reset through reverse CODE scan, lseek and return at 0x80004eb0; length 764, fd position 57, selected ownership/runtime/source frames | 80 new registrations; 3,545 jobs; 80 focused (78 allowed, two pure); 2,157 generated outputs and ELF pins; `logs/code-scan-*` |

`d9c0be7b` passed the 6,248-job gate and is published in `91e7083b`.
The CODE worker was stopped after its checks and notes were complete and
it remained quiet with no active command. Reviewed source hashes were
unchanged; its task was preserved and committed. Only additive dead-end
notes conflicted on rebase, and both were retained.

Each focused list was checked exactly against its registrations and allowed
axioms, and all six handoffs passed their full integration gates. Rebase conflicts were
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
| `syo-wt/a1-prims-next` | Lead validation of full parser/caller, worker stopped after completed core/focused checks | `/tmp/syo-format-lead-affected-launch.log` |
| Lead | Gate, independent review, next-task contracts and integration | main and bprime |

The parser/caller modules and 52 focused reports pass (49 new theorems).
Cold rebuilding unchanged SnpSvf hit the 10 GiB early guard. Lead verified
all 551 repository sources in SvfLong's import closure are unchanged, stopped
the worker with no active command, and copied the verified idle gate cache
to the idle lane after provenance/lock checks. New semantic facts were moved
unchanged to IntegerFormatFacts, restoring Data.lean byte-for-byte. Lead is
rebuilding changed modules plus AllocSprintfNative under the same cap.
Evidence: `logs/format-native-*`, `logs/format-svflong-source-comparison.json`.
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
