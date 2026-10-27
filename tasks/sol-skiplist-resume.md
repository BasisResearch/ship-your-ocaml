Binding rules: read CLAUDE.md and relevant PHASES.md, PLAN.md and lane-log sections; user directions override older briefs.
Run scripts/abs_inventory.sh before proof work; reuse mandatory abstractions by name.
No sorry, axiom, native_decide, bv_decide, heartbeat increases, or edits to generated outputs.
Edit generators; audit new theorems with only propext, Classical.choice, Quot.sound.
Before each build check free -g (available >=25 GB); one build per worktree.
The launcher encloses this worker and all builds in systemd MemoryMax=12G, LEAN_NUM_THREADS=2.
Run Lean with scripts/lean-capped.sh lake ...; it uses the inherited cap or creates a 12 GB scope.
Do not add ulimit -v: virtual reservation breaks the large import closure; the cgroup enforces 12 GB.
Work only in this worktree; preserve inherited WIP and never force-push or reset it away.
BarrierGrowthFull stays with G2; CustomMemCall remains a named premise; C4 round 2 waits for F1.
Read docs/lanes/DEAD-ENDS.md before choosing a route; record newly refuted routes there.
Build affected modules and a focused #print axioms file; register audits, but leave full OCaml.Audit to the lead gate.
Update lane log/PHASES accurately; leave checked edits for lead review.
The lead commits and lands via scripts/integrate.sh; this sandbox makes Git metadata and the landing queue read-only.
Keep reads targeted (rg, bounded sed); do not scan home or print whole huge ledgers or audit logs.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: finish the preserved first empty-skiplist insertion native summary, repairing its evaluator proof to stay below the 12 GB cap.
Files: OCaml/Vm/Gc/SkiplistFirst.lean; generated Boot/Startup/SkipFirst* (edit scripts/gen_startup_rows.py); lane log, PHASES and audit.
The previous worker was killed by the cgroup OOM limit at 18:42:17 UTC on October 27, not by a usage limit. Its WIP has been committed intact.
Read /tmp/skipfirst-eval.log and the tail of logs/sol-a6-gc-20261027-182437-997318.log in the main repo. Generated rows built, but SkipFirstEval did not complete.
Do not repeat the same monolithic simp certificates: factor evaluator normalization into small reusable lemmas/chunks in the generator and validate them separately; keep heavy compilation serialized.
The actual startup seed 0 becomes 25173, chooses level 0 and requests a 24-byte cell. Reuse the generated rows, block_summary, stat_alloc_ready, native frames and selected live-block ownership.
Continue the existing prefix proof, allocation call, cell/header stores and ABI return. Retain explicit room, key/frame bounds and precise memory/output effects.
Done: checked first-insertion native summary with the startup key witness, allocator/owned-block frame, focused standard-axiom audits and generator drift check.
Do not claim full Skiplist.Ops, arbitrary insertion/removal, RootsAt or reset composition; list what remains. Avoid assumed runs/posts and never raise budgets.
Leave checked edits for lead review and integration.
