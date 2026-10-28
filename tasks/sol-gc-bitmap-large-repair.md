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

Target: repair the checked high-bitmap interface gap, then execute the original-entry least-large split/return requested by sol-gc-large-split-entry.md using the repaired invariant.
Prerequisite: BestFitEntryLarge.highBitmapMemory_obstruction is present. Files: Gc/{BfShape,BestFitPreservation,BestFitEntryNext,BestFitEntrySmall,BestFitEntryLarge,BestFitLargeComplete,BestFitFallbackLarge,BestFitLargeAccess,BestFitLargeFootprint,BestFitNextAudit} and existing startup bitmap producers.
Keep the old SmallRepresentation and its counterexample meaningful. Introduce a named bounded-bitmap refinement (bits 16..31 clear / mapBits.toNat < 2^16) and an explicit bounded representation, rather than claiming the old MapConsistent already constrains those bits.
Prove the refinement from actual zero-map startup observations available in the repository, with their exact scope (a captured-memory witness is not reset execution). Prove preservation through actual exact clear/unchanged and next-size clear/set bitmap logs, including remainder insertion. No caller initialization is claimed without its native producer.
Derive filtered request bitmap = 0 from positive request <=16, the refined representation and no nonempty list at/above request, allowing nonempty lower classes. Use the actual LW sign extension and 32-bit shift/mask expression; do not assume an intermediate zero observation.
Reuse BestFitFallback.allocate_large for original missing entry -> filtered-zero -> least tests -> bf_split -> original RA. Its existing branch is request<=16 and request+17<sourceSize only.
Supply LargeConditions on the searched snapshot from original least pointer/header/size, original write/native windows, actual saved-bank frame and physical separation; do not accept arbitrary intermediate/final states.
Return unchanged bounded small representation, shortened large extent/header, actual allocated separation from all small extents and the remaining large block, exact counter/log, code/output and RA/SP/GprsSame. Any singleton-tree specialization and natural counter credit must be explicit.
Done: checked bounded-bitmap invariant/producer/preservation and original-entry sufficiently-large split with returned physical facts, focused affected build and all-new-theorem audit. If the packet must stop at a concrete seam, identify the exact remaining original-entry derivation; do not resend the already proved old-interface obstruction.
This repairs an internal representation, not GoodF1. Keep CustomMemCall named, full BarrierGrowthFull with G2 and C4 round 2 waiting; remaining tree branches, requests>16, colors, caller production and collection stay open.
Update PHASES/a6-gc/DEAD-ENDS precisely; leave checked edits for lead review/integration.
