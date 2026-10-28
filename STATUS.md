# Foreman status

Updated 2026-10-28 19:12 UTC. Target: close Layer A for `GoodF1`, with G2 continuing.

## Needs user

None currently. Work continues; no user-only decision blocks the next steps.

## Current result

The reviewed local counted table is **133/134**: complete `C_CALL1` is checked;
`C_CALL2` remains. Published coverage is **132/134** until the queued batch
passes integration. Neither count establishes reset-to-Loaded or full G2.

Standing decisions: `BarrierGrowthFull` remains G2; `CustomMemCall` remains a
named premise; C4 abstraction-discovery round 2 waits until F1 closes.
GoodF1 has not been narrowed to simplify named registration or formatting.

## Published and landing

`origin/main`: **`29994e71e449eb89c336180dc4e82adc0357e3ec`**, independently
verified after the 17:47 UTC gate. That gate passed 6,208 jobs, 9,736 main
allowed-axiom reports (9,740 including TCB), 150 axiom-free reports and 329
OS traces: 5,069 steps, 324 accepted, five special, zero rejected/unsupported.
The whole build has 12,196 allowed-axiom reports including imported audits.
Evidence: `logs/{integrate,build}-29994e71.log`, `logs/gate-29994e71.json`.

**Active gate:** bprime at fixed candidate `4c4209ea`, started 17:47 UTC,
for physical custom-state/read-context changes (`53e93d16`). Its Layout
changes trigger a broad rebuild; no error has been reported. Log:
`/tmp/syo-custom-physical-integrate.log`; bprime `.integrate.log` and
`.check-build.log`. Do not change this tree's HEAD, source or cache mid-gate.
Later reviewed commits below are queued for the following gate.

All publication goes through `scripts/integrate.sh` and normal fast-forward
pushes to origin/main. Reviewed snapshots remain on `keep/*` branches.

## Reviewed commits awaiting publication

| Commit | Result | Lead-reviewed evidence |
| --- | --- | --- |
| `53e93d16` | Physical custom state, exact read-only call pins, footprint/accounting/frame laws and captured counted startup entry | 45 new registrations; 3,679-job consumer build; 62 focused reports (59 allowed, three pure); `logs/custom-physical-*` |
| `66343b8a` | Selected custom reserve/spending on one returned ledger; concrete listing runtime relative only to CustomMemCall | Six new registrations; 3,682 jobs; 144 focused (126 allowed, 18 pure); `logs/custom-credit-*` |
| `2165d4de` | Current CODE descriptor/file/image observations derived from actual reset initialization, without later-memory matching premises | 37 new registrations; 3,533 jobs; 37 focused (36 allowed, one pure); `logs/code-source-*` |
| `9f4e4fa1` | Concrete channel-opening runtime and counted in/out adapters, relative only to CustomMemCall | Nine new registrations; 3,683 jobs; 161 focused (141 allowed, 20 pure); `logs/opening-runtime-*` |
| `ce120d18` | Original-caller bounded least-large allocation wrapper, actual color/header, remaining representation, exact counters/log/ABI | 39 new registrations; 1,419 jobs; 43 focused (40 allowed, three pure); `logs/a6-wrapper-*` |
| `26201d6b` | Complete counted C_CALL1 using concrete ordinary/channel/counter/flush returns and actual native exit; table 133/134 | Four new registrations; 3,733 jobs; 22 focused (21 allowed, one pure); `logs/counted-unary-*` |

Each focused list was checked exactly against its registrations and allowed
axioms; the full integration gate remains required. Rebase conflicts were
additive lane/dead-end notes and retained both sides. Snapshot branches:
`keep/custom-physical-reviewed-20261028`,
`keep/custom-credit-listing-reviewed-20261028`,
`keep/startup-code-source-reviewed-20261028`,
`keep/opening-runtime-reviewed-20261028`,
`keep/g2-large-wrapper-reviewed-20261028`,
`keep/counted-unary-reviewed-20261028`.

## Active workers and next tasks

At most two separate **gpt-6.1-sol / high** CLI workers; no built-in proving
agents. `codexwork.sh` checks available memory and encloses each worker and
its builds in a 12 GB systemd scope. Builds use `lean-guarded.py` and
`lean-capped.sh`; one build per tree, at least 25 GB available before launch.
No active worker cache is copied into bprime.

| Slot | Current task | Log |
| --- | --- | --- |
| `syo-wt/a6-gc-next2` | Actual CODE reverse scan, lseek and return, including CRCS/CODE second-byte mismatch | `logs/sol-a6-gc-next2-20261028-184250-2791879.log` |
| `syo-wt/a1-prims-next` | Full native format parser including l/n/L and actual signed/unsigned caller prefix to alloc_sprintf | `logs/sol-a1-prims-next-20261028-184554-2825386.log` |
| Lead | Gate, independent review, next-task contracts and integration | main and bprime |

The parser worker resumed output after a quiet interval; it is active.
Current task files: `tasks/sol-code-seek-scan.md`, `tasks/sol-format-parse-all.md`.
Next G2 rotation: `tasks/sol-g2-small-wrapper.md` (original exact/next-small
wrapper, factoring common caller frames). Next primitive rotation:
`tasks/sol-named-reserve.md`; subsequent formatting decoder work is in
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
- **Reset to Loaded:** actual CODE scan/lseek (active), CODE allocation/read,
  code fragments/digest, PRIM, DATA unmarshalling, promotion and system/argv.
  Current source/descriptor/file observations at the scan entry are reviewed.
- **G2:** small original wrappers, remaining tree/size cases, requests>16,
  heap expansion, caller invariant production, full allocator readiness and
  collection. The counted table requires returned custom-count preservation
  in `BarrierGrowthFull`; the base-layout contract alone cannot supply it.

Detailed completed work and residuals remain in PHASES.md and the lane logs;
older publication evidence remains in `logs/gate-*.json` and raw logs.
