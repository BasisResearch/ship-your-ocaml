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

Target: prove the first empty-skiplist insertion used by caml_init_backtrace, as a native summary with explicit allocator room.
Files: OCaml/Vm/Gc/Skiplist.lean and a new SkiplistFirst module; scripts/gen_gc_rows.py (or startup generator); OCaml/Vm/Boot/Startup/AtomTableReset.lean; relevant lane logs.
The reset milestone returns at 0x80004e80; caml_init_backtrace at 0x8000ef3c tail-calls caml_register_global_root, which inserts Caml_state+256 into caml_global_roots.
Inspect existing generated rows and reuse block_summary, indexed_loop, stat_alloc_ready and native-frame/heap abstractions.
Start with the all-zero header and seed/state actually supplied by startup; retain explicit capacity for the cell allocation, key, frame, memory and ABI posts.
Do not claim general Skiplist.Ops: its current insert field quantifies over arbitrary cap without a room premise, so reconcile that interface before any full-operations claim.
Done: a checked first-insertion native summary, allocator/owned-block frame, and level-0 key witness suitable for reset composition; focused audits and generator drift pass.
Record precisely the remaining arbitrary-list insertion, removal/empty, RootsAt and reset-call composition obligations. Avoid an assumed run or an assumed desired post.
Leave checked edits for lead integration; keep this task to first insertion.
