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

Target: return the actual small free-list representation and allocated-extent separation from every existing exact-size allocator branch, then compose exact/next-size original-entry dispatch.
Files: Gc/{BestFitExact,BfShape,BestFitPreservation,BestFitEntryNext,BestFitNextAudit}.lean and a new bounded exact/entry composition module if needed.
BestFitExact.allocate already executes all four exact-size branches (empty/nonempty successor and repaired/unchanged cursor) from bf_allocate entry. Reuse it; do not regenerate or reprove its native run.
Derive its Conditions via BfShape.exact_of_nonempty from the original represented selected list, and derive its register/native inputs from one original-entry interface.
Return SmallRepresentation after.σ.mem (BfShape.popped lists s bs), original selected header/size, and AllocatedApart for the actual returned header; retain native stack/ABI/output and exact effect.
Use SmallShape.pop, SmallHeaders.pop, SmallPhysical.pop/selected_apart, MapConsistent.clear and existing scalar/write-log frame laws. Each cursor/bitmap/counter write must be justified from the actual branch log; do not assume a final map or header observation.
Add a shared original-entry small-success theorem selecting the exact branch when lists request is nonempty, otherwise the already checked EntryNextInput/search route from a nonempty larger list. Its output must carry the selected returned representation in both branches.
Use named input/post structures, FnSummary, GprsSame and LiveFrame. Avoid a large dependent branch/whole-memory simplifier; factor branch log observation helpers first.
If natural free-word accounting is included, expose actual sufficient credit separately; SmallRepresentation alone does not relate the modular counter to free extents. Do not claim caller initialization or full allocator readiness.
Done: checked original-entry exact/next-size dispatch for positive requests <=16 when a suitable small list exists, with preserved full SmallRepresentation and allocated separation; affected builds, focused all-new-theorem audits and accurate remaining G2 ledger.
Zero-filtered bitmap/large-tree, other sizes/colors, native major initialization, caller invariant production and collection remain separate. Counted BarrierGrowthFull stays G2 and must eventually preserve cp/world counts, not only base runtime.
Record dead ends and leave checked edits for lead integration; do not add stronger GoodF1 guards or arbitrary intermediate/final states.
