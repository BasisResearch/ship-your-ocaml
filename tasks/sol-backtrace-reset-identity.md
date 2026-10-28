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

Target: retain and expose the actual ELF-reset witness through the checked reset-to-backtrace chain, removing the existential interface loss before further startup extension.
Files: Boot/Startup/{Reset,ResetSetup,ReadSectionsReset,InitGcReset,InitStackReset,AtomTableReset,BacktraceReset}.lean and focused startup audit; use rg for actual reset setup module names.
The early Reset* structures retain a nested ElfResetReady elf initial witness. reset_init_stack_reset_exists currently returns only Steps (fillZero initial) after plus the stack post; atom/backtrace producers then forget reset identity. Do not infer reset identity from Steps alone.
Strengthen the producer chain or add structured stronger variants that carry ElfResetReady for the pinned parsed ELF to the final ResetBacktrace. Keep older existential APIs as projections where helpful.
Derive the witness by following the real nested ResetReadSections/Attempt/Open/Parameter source, without assuming a new reset fact. Preserve the checked domain ownership, root globals, page table and capacity facts from the preceding worker.
Then provide the actual reset-to-backtrace theorem for every initial config satisfying the existing ElfReset for that parsed ELF, using setup determinism/metadata congruence as appropriate; do not assume equality of arbitrary initial configs without proving it.
Inspect whileMin_reset_loaded_Statement and expose exactly the reset-facing interface its eventual continuation needs. Preserve fillZero and actual native Steps.
Done: checked reset-qualified backtrace reachability with standard-axiom audit, affected build and a precise statement of the remaining path from 0x80004e84 to Loaded. Full reset-to-cut remains open.
Record the dropped-witness contract issue in DEAD-ENDS as interface inspection, not a counterexample to execution. Do not add a captured-state or later-state premise to hide it.
Leave checked edits for lead review/integration.
