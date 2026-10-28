Binding rules: read CLAUDE.md and relevant PHASES.md, PLAN.md and lane-log sections; user directions override older briefs.
Run scripts/abs_inventory.sh before proof work; reuse mandatory abstractions by name.
No sorry, axiom, native_decide, bv_decide, heartbeat increases, or edits to generated outputs.
Edit generators; audit new theorems with only propext, Classical.choice, Quot.sound.
Before each build check free -g (available >=25 GB); one build per worktree.
The launcher encloses this worker and all builds in systemd MemoryMax=12G, LEAN_NUM_THREADS=2.
Run Lean via python3 scripts/lean-guarded.py --log /tmp/<task>.log -- scripts/lean-capped.sh lake ...; the guard stops failed/10 GiB builds.
Do not add ulimit -v: virtual reservation breaks the large import closure; the cgroup enforces 12 GB.
Work only in this worktree; preserve inherited WIP and never force-push or reset it away.
BarrierGrowthFull stays with G2; CustomMemCall remains a named premise; C4 round 2 waits for F1.
Read docs/lanes/DEAD-ENDS.md before choosing a route; record newly refuted routes there.
Build affected modules and a focused #print axioms file; register audits, but leave full OCaml.Audit to the lead gate.
Update lane log/PHASES accurately; leave checked edits for lead review.
The lead commits and lands via scripts/integrate.sh; this sandbox makes Git metadata and the landing queue read-only.
Keep reads targeted (rg, bounded sed); do not scan home or print whole huge ledgers or audit logs. While builds run, tail a few log lines; do not repeatedly print full git diffs.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: supply original-caller exact/next-size small success for caml_alloc_shr_for_minor_gc, preserving the actual bounded free-list representation through header/color/accounting and caller restoration.
Prerequisite: reviewed AllocEntryLarge wrapper handoff. Reuse BestFitEntrySmall/BestFitEntryNext, AllocWrapper/AllocExact, AllocFinish, AllocSuccess, AllocWrapperCore and the new original-caller read/frame helpers.
Files: Gc/{BestFitEntrySmall,BestFitEntryNext,BestFitPreservation,AllocWrapper,AllocExact,AllocFinish,AllocEntryLarge} plus a dedicated original-small wrapper module and audit.
Scope: positive requests <=16 with a suitable represented small class. Cover the existing exact-size branches and the existing next-size dispatch; keep no-suitable least-large, arbitrary large-tree search, requests>16, expansion and collection separate.
Use an original-state interface with actual wrapper registers/code, bounded representation, relevant physical source/native-frame separation and explicit no-major-slice/free/allocated counter credit. No assumed intermediate configuration/run, whole AllocWrapper.Conditions or opaque returned invariant.
Factor shared prologue, accounting-read and caller-frame transport from the reviewed large wrapper before duplicating it. Reuse reflected LogInW/window composition, LogWindows, selected LiveFrame and existing finish/return summaries; never reprove native free-list execution.
Derive actual prepared representation and native search/finish conditions from those original inputs. Retain the selected exact popped or next-size remnant family and prove bounded bitmap preservation from the actual clear/set effects.
Return exact native size/tag/phase-selected color (HeaderOk alone omits color), allocated separation, actual remaining representation, original RA/SP/saved registers, output and the composed write log. State natural counters only under original nonoverflow/nonunderflow credit.
Full allocator ownership/global readiness is not implied by geometric source bounds; carry an explicit selected ledger only where its frame is needed. Preserve the existing high-bit obstruction and the stronger bounded invariant.
Done: checked original-wrapper small-success summary, affected wrapper/allocator consumers and all-new-theorem focused audit. Update PHASES/a6 log/DEAD-ENDS, naming any precise residual; no full G2 or BarrierGrowthFull closure claim from this branch.
Keep GoodF1 unchanged, CustomMemCall named and C4 round 2 waiting. Leave checked edits for lead review/integration.
