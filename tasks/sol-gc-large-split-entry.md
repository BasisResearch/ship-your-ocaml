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

Target: supply original-entry zero-small-bitmap routing into the existing least-large split/return and preserve the selected free extents, for the already implemented sufficiently-large least-block branch.
Prerequisite: BestFitEntrySmall and the shared EntryInput are present. Files: Gc/{BestFitEntryNext,BestFitLargeComplete,BestFitFallbackLarge,BestFitLargeAccess,BestFitLargeFootprint,BfShape,BestFitPreservation,BestFitNextAudit}.lean and a bounded original-entry large module.
Reuse BestFitFallback.allocate_large, which already executes missing entry -> filtered bitmap -> least-block tests -> bf_split -> original return. Do not regenerate or reprove that run. Its current Conditions require request <=16 and request+17 < sourceSize; this task does not cover larger requests or the remaining tree alternatives.
Derive the actual missing slot and zero filtered bitmap from SmallRepresentation, positive request <=16 and no nonempty class at or above the request. Keep lower-size lists allowed; do not silently assume all small lists empty.
Use one original-entry large-block observation/ownership structure: actual least pointer, source header/size, header write window, heap/native-stack separation, and physical separation from represented small extents. Supply LargeConditions on searched R c, headerOutside and ReturnOutside from the real saved-bank log and those source facts, not arbitrary intermediate-state observations.
Return the actual original-header-derived allocated address, unchanged SmallRepresentation for lower classes, the shortened remaining large extent/header, and allocated separation from both small lists and that remaining extent. Track exact native counter/log, RA/SP, code/output and GprsSame/LiveFrame using existing abstractions.
If retaining least/tree topology, isolate its actual observed fields and prove the real split writes preserve them. A singleton large-tree specialization must be explicit; do not claim arbitrary tree preservation from one header update.
Keep natural free-word credit explicit and derive subtraction from the native modular counter only under that credit; representation alone is insufficient. No new caller-initialization assumption should be presented as a producer.
Done: checked original-entry least-large split/return with derived zero-bitmap/setup obligations and returned physical representation/separation; focused affected build, all-new-theorem audits and an accurate G2 ledger.
Other large-tree branches, requests >16, colors, original caller/invariant production, full readiness and collection remain open; counted BarrierGrowthFull remains G2. Do not change GoodF1 or CustomMemCall.
Record failed routes and leave checked edits for lead review/integration.
