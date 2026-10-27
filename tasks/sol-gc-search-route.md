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

Target: compose native next-size bitmap search with BestFitNext.allocate_next, from BestFitFallback.pc (0x800073cc) to the original caller.
Files: Gc/{BestFitFallback,BestFitNext,BestFitNextRoute,FfsLowest,BfShape}.lean or a small assembly module; generated instructions only through gen_gc_rows.py.
Start from checked route 78081098. Reuse search_nonzero and allocate_next; retain actual branch logs and explicit remaining allocator obligations.
Use original data/geometry with positive request, small-list shape, SmallHeaders and MapConsistent, plus existence of a nonempty larger size <=16. Derive the lowest filtered bitmap bit and selected size/head from these facts.
Do not assume FfsLowest.Lowest, Found, RouteInput at the later state, saved stack readbacks or a desired return as unexplained entry fields. Prove the bit-selection lemma and transport from the actual search prefix's log.
Derive saved bitmap/request/original RA and the 32-byte frame from generated fallback stores; preserve header/list/map/code facts through that real prefix and the ffs call.
Compose the native return, result header, final stack/ABI/output and branch-dependent counter. Retain exact combined logs and selected LiveFrame under explicit original ownership separation.
Use shared GprsSame, bounded read/log/access certificates, and existing frame abstractions. Do not repeat broad normalization routes in DEAD-ENDS or raise budgets.
Done: one checked search-to-native-return summary with actual input producers, focused affected builds and standard-axiom audits, generator/discipline checks and precise ledger.
Dispatch into fallback, final reinsertion preservation of the allocator invariant, other size classes, allocation colors and collector integration remain open. Do not claim full allocator/BarrierGrowthFull closure.
Leave checked edits for lead review and integration; preserve GoodF1.
