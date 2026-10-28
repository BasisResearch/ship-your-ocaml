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

Target: prove the next-size best-fit split after BestFitNext.pop, through the remnant call and its return continuation.
Files: OCaml/Vm/Gc/BestFitNext.lean, BestFitRemnant.lean, BfShape.lean, Generated/BestFitSplit.lean (generator-owned), scripts/gen_gc_rows.py; lane log and PHASES.
Start from the checked pop post at 0x800074e8; reuse generated segments and block_summary, FnSummary call composition, and named frame/readback abstractions.
Supply the concrete split header/payload writes, exact remaining free words, small remnant insertion preconditions and resulting frame; do not assume the intended split post.
BestFitRemnant.insert is checked standalone; inspect whether its wrapper/phase cases also need composition for this caller, and account for each actual branch.
Use BfShape.SmallShape.pop and MapConsistent.clear only after supplying their frame/readback premises; do not treat structural preservation as automatic.
Done: a checked native split/call/return summary suitable for chaining search-pick-pop, focused build and standard-axiom audits, generated drift check, accurate remaining-obligation ledger.
Full allocator readiness, remaining size classes, allocation-color/GC integration and BarrierGrowthFull stay explicitly open until actually supplied. Keep GoodF1 unchanged.
Leave checked edits for lead review/commit/integration.
