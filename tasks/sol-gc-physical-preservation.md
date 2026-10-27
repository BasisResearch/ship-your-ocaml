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
Keep reads targeted (rg, bounded sed); do not scan home or print whole huge ledgers or audit logs.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: preserve the new SmallPhysical component through the checked native next-size allocator route so its representation theorem can be reused on later allocations.
Files: Vm/Gc/{BfShape,BestFitPreservation,BestFitNextAudit}.lean; reuse BestFitNextRoute/BestFitSearchRoute posts and exact routeLists/searchLists.
The current result preserves SmallShape/SmallHeaders/MapConsistent and AllocatedApart, but consumes SmallPhysical without returning it. Do not call that a complete reusable allocator invariant.
Prove original occurrence-based extent bounds/disjointness survive selected-head removal. For insertion, derive bounds and separation of the smaller remnant from the original selected block and its actual decoded size; cover zero-word and sweep-deferred branches.
Produce RoutePost.physical and SearchReturned.physical for the actual final list family, using existing stage witnesses and original input. Retain existing result/ABI/counter and representation statements without new final-state premises.
Add a compact combined representation result if it removes duplicated caller obligations. Derive the empty-list base case; do not claim native initialization or caller production solely from that pure lemma.
Do not replace occurrence separation with pointer inequality, assume final uniqueness, or raise proof budgets. Use existing selected_apart, popped_mem, size/readback facts and bounded arithmetic.
Done: checked final SmallPhysical at the same native return, focused affected build/allowed-axiom audit, accurate G2 ledger and precise next entry/dispatch obligations.
Production of the full invariant from major-heap initialization, original dispatch, other size classes/colors, natural free-space accounting and full collection remain open; BarrierGrowthFull stays G2.
Leave checked edits for lead review/integration.
