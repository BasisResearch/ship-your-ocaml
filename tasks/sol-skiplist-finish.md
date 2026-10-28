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

Target: finish the first empty-skiplist insertion from the checked prefix through the actual allocator call, four stores and native return.
Files: OCaml/Vm/Gc/SkiplistFirst.lean, shared startup allocator-frame helpers, scripts/gen_startup_rows.py; relevant lane log, PHASES and audits.
The prefix/evaluator checkpoint is preserved. Reuse prepare and generated checkedLogStep/checkedLogStore certificates; never retry the broad simp that twice hit 12 GB.
The JAL at 0x8002acbc targets caml_stat_alloc at 0x8000bb2c: splice stat_checked, not stat_alloc_ready (which proves the noexc entry).
Use explicit allocation capacity and selected owned blocks; obtain the 24-byte cell from the real allocation result and derive all suffix memory pins from its frame.
The suffix writes key, zero data, zero next pointer and the global-roots head, then restores the caller. Prove exact scalar readbacks, ABI, cell ownership and outside-memory effects.
LocalFrame.output is equality of Vsa.Machine.output (String.join of sailOutput), not equality of raw output vectors; do not infer the latter from that contract. Preserve the observable output directly, or supply a real stronger shared frame proof if a consumer requires it.
Use NativeFrame, GprsSame, LiveFrame and block_summary/standard FnSummary call composition. Never assume the desired callee or suffix post.
The startup key is Caml_state plus the generated backtrace_last_exn offset; distinguish its actual startup witness from a captured final-state snapshot.
Use python3 scripts/lean-guarded.py for diagnostics/builds; diagnostic lean -M 6000 -j 1, all runs inside the 12 GB worker cap. Avoid adding unrelated captured-image imports solely for a numeric witness.
Done: a checked full first-insertion native summary with non-vacuous startup key/capacity witness, selected ownership/frame, standard-axiom audits and generator drift pass. The prefix alone is already available.
General Skiplist.Ops, arbitrary insertion/removal, RootsAt and reset composition remain separate obligations. Leave checked edits for lead review and integration.
