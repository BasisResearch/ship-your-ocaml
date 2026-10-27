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

Target: finish the preserved next-size best-fit split/remnant/return composition, repairing its evaluator without exceeding memory limits.
Files: Gc/{BestFitNext,BestFitRemnant}.lean, Generated/BestFitSplit.lean and scripts/gen_gc_rows.py; audit and lane ledger.
The first split worker hit its 12 GB cap at 20:55:32 UTC on October 27 (run-p4087439-i464873190.scope); its WIP is committed. Do not rerun the unchanged broad build.
Generated BestFitSplit passed 609 jobs (/tmp/a6-next2-build.log); the subsequent BestFitNext build died before emitting diagnostics (/tmp/a6-next2-next.log).
First isolate the failing declaration in a temporary source prefix using the guard, lake env lean -M 6000 -j 1 --profile. Reuse scalar/log certificates, not broad state reduction or budget increases.
Then complete the actual run from pop's post at 0x800074e8 through the remnant wrapper and native return. Reuse generated block_summary and FnSummary call composition.
The wrapper covers zero size, sweep deferral, and insertion with/without cursor repair. Derive the split header, reduced free-word counter, saved result and return-word readbacks; no assumed split or remnant post.
Use the actual memory/frame effects to supply BfShape.SmallShape.pop and MapConsistent.clear premises; retain allocator ownership and exact relevant branches.
Done: checked native split/call/return summary suitable for search-pick-pop, affected capped build, focused standard-axiom audits, generator drift check, accurate lane/PHASES entry.
Full allocator readiness, other size classes, allocation-color/GC integration and BarrierGrowthFull remain explicitly open. Preserve GoodF1 and record new dead ends.
Leave checked edits for lead commit and integration.
