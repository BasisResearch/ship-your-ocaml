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

Target: extend the proved universal ELF-reset prefix through interpreter/debugger initialization to native PC 0x80004e94, retaining the actual producer history for later CODE loading.
Files: Vm/Boot/Startup/BacktraceReset.lean and new interpreter-init composition modules; scripts/gen_startup_rows.py owns all generated rows/audits.
The actual main continuation at 0x80004e84 sets a1=a0=0, calls caml_interprete at 0x80004e8c (RA 0x80004e90), then calls caml_debugger_init (RA 0x80004e94).
The pinned interpreter saves registers in its 528-byte frame, takes the a0=0 branch at 0x80001e30 via 0x80001e34 to 0x800035e0, and restores/returns. No threaded-code initialization is in this ELF. Debugger init at 0x80021614 is one ret.
Reuse existing entry/return generated rows if compatible; otherwise generate bounded regions from the ELF with gen_fn and compose FnSummary, GprsSame and LiveFrame. No handwritten instruction proofs or captured-state execution substitute.
Produce named input/post structures with the actual memory log, ABI, heap/runtime readiness, tick/HTIF/output and caller stack preservation. Derive every precondition from ResetBacktrace.done and its real producer chain.
Retain a ResetBacktrace witness in the new reset post, its ELF-reset identity, and actual Steps. Export universal reset reachability in the same form as whileMin_reset_backtrace.
For later CODE/primitive/DATA loading, retain the actual section-descriptor/fd/argv ancestor witness and prove only frames supported by these native stores; do not add arbitrary original-state facts as new assumptions.
Done: checked native reset-to-0x80004e94 composition, affected build and focused allowed-axiom audits, generated checks, accurate ledger/lane log and next CODE-load obligations. This does not close reset-to-Loaded.
Record any missing inherited supplier precisely and strengthen its real producer if needed; preserve previous existential APIs as projections. Leave checked edits for lead integration.
