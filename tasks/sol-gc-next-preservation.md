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

Target: prove preservation of the represented small free lists/headers/bitmap after the checked native next-size allocation, including actual remnant reinsertion or deferral.
Files: Gc/{BfShape,BestFitRemnant,BestFitNext,BestFitNextRoute,BestFitSearchRoute}.lean and one focused preservation/audit module if useful.
Reuse SearchReturned/RoutePost stage witnesses and exact native logs; do not rerun instruction proofs. Start with the actual remnant InsertPost/Post representation rule, then compose the split/pop/search route.
Define the final list family by popping the selected head and inserting the remnant at its decoded size exactly when BestFitRemnant.Inserts holds. Retain the zero-word and deferred sweep branches.
Carry SmallShape, SmallHeaders and MapConsistent to the actual returned memory, with the counter equation already proved. Derive all intermediate header/link/readback facts from the logs.
SmallShape alone has no full free-block separation. If required, add an explicit original physical block-extent/disjointness component; derive intermediate nonaliasing from it. Do not assume desired final shape, post-list uniqueness, or unexplained intermediate OutL facts.
Keep the selected allocated result disjoint from represented remaining free blocks, and state precise original bounds required for nonwrapping extents. Do not pretend caller production of a new physical invariant has already been proved.
Use bounded scalar/log/access certificates and shared frame abstractions. Read DEAD-ENDS; no whole-memory normalization or raised budgets.
Done: checked native-return preservation of small-list/header/bitmap representation for every existing next-size remnant branch, focused builds/allowed-axiom audit, and an accurate G2 ledger entry.
Other size classes, original dispatch, allocation colors, complete allocator readiness and full collection remain open. BarrierGrowthFull stays G2; do not weaken GoodF1.
Leave checked edits for lead review/integration.
