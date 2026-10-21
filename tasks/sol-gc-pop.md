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

Target: finish and validate BestFitNext.pop, the next-size small-list allocation path's head removal.
Files: OCaml/Vm/Gc/BestFitNext.lean; BestFitRemnant.lean; BfShape.lean; OCaml/Audit.lean; docs/lanes/a6-gc.md; PHASES.md.
Preserved work includes the checked BestFitNext.pick commit and unvalidated stage-2 pop implementation.
First build OCaml.Vm.Gc.BestFitNext under scripts/lean-capped.sh; fix concrete failures at default proof budgets.
Reuse generated bf_allocateX74bcT/F and bf_allocateX74cc segments plus block_summary; do not re-prove instruction spans.
Done: pick and pop native summaries compile, new theorem axioms are standard, and the ledger accurately records which later splitting/callee obligations remain.
Keep this task to stage 2; leave later splitting and overall allocator readiness open.
Leave checked edits for lead review/commit/integration; do not attempt Git writes or home queue operations inside the sandbox.
