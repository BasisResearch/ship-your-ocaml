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

Target: compose BestFitNext.pick, pop and the checked split_return into one native next-size route from pickPc (0x800073f8) to the original allocator caller.
Start after the split/remnant worker is checked and committed. Preserve its explicit branch accounting and readback contracts; inspect the final lane entry.
Files: OCaml/Vm/Gc/BestFitNext.lean or a small assembly module, BfShape.lean, BestFitRemnant.lean and generated inputs through scripts/gen_gc_rows.py.
Derive each later input from the actual preceding post and original data/geometry: selected head/size, requested words, stack saves, bitmap observation, code pins and header/link frames.
Use a single entry predicate over the original memory plus the small-list/map shape. Do not assume PickPost, PopPost, SplitPrepared, later callee inputs or a desired final run as original premises.
The selected source size must be strictly larger than the positive request and <=16; derive the header/size agreement from the represented selected list rather than adding unexplained intermediate facts.
Compose exact memory logs and their observations through both merge-cursor branches, empty/nonempty pop and all remnant-wrapper branches. Retain original ABI/output, result location, remaining counter and selected LiveFrame.
Reuse the now-checked PopPost.shape/map_clear and bounded access/log certificates. Never re-expand the OOM split_writes/split_access route; diagnose through the guard and -M 6000 -j 1 if needed.
Done: a checked single native summary usable after bitmap search, with actual input producers, focused affected builds/standard-axiom audit, generator checks and accurate remaining-obligation ledger.
Bitmap search/route dispatch before pickPc, other size classes, full allocator readiness and collector/color integration remain open until supplied. Do not claim BarrierGrowthFull or full allocator closure.
Leave checked edits for lead review/commit/integration; preserve GoodF1 and record new dead ends.
