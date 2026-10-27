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

Target: extend the actual reset-through-atoms execution through caml_init_backtrace and its global-root registration, using the checked first empty-skiplist insertion.
Start only after the first-insertion summary is checked and committed; inspect its exact capacity, key, frame and output contract before choosing the composition.
Files: OCaml/Vm/Boot/Startup/AtomTableReset.lean and a new backtrace/startup continuation module; OCaml/Vm/Gc/SkiplistFirst.lean; scripts/gen_startup_rows.py and relevant generated call rows.
Use gen_fn.py / the existing startup-row generator for caml_init_backtrace, its register_global_root wrapper and the actual caller continuation from the atom-table return at 0x80004e80.
Read the ELF's real call targets and generated Layout fields; never substitute a different allocator or root-registration entry because its interface looks similar.
Derive domain-field initialization, the backtrace_last_exn key and initial value, empty header/seed, selected owned-block ledger and allocation room from the actual preceding run.
The current reset_init_atom_table_returned_exists existential forgets domain ownership and low-memory data; strengthen its producer chain (InitStackReset / AtomTableDone) to retain them, rather than adding initial assumptions.
Compose the checked first insertion and derive its postcondition from that run. Carry HeapReady/LiveFrame, native ABI, code/image and observable output through the return.
Do not use the captured final memory or Loaded snapshot as evidence that initialization executed. Reuse the existing reset prefix and shared GprsSame/LiveFrame abstractions.
Done: a checked reset-to-after-backtrace summary with explicit next native PC and preserved allocator/domain/global-root facts, focused build/standard-axiom audits and generator drift pass.
Interpreter/debugger initialization, the later argv root registration, complete reset-to-cut/Loaded and general Skiplist.Ops remain separate until supplied. Leave checked edits for lead integration.
