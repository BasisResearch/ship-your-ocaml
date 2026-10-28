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

Target: finish the interrupted full decimal native alloc_sprintf summary, retaining its successful proof composition.
Read tasks/sol-alloc-sprintf-decimal.md for scope. Files: Format/{AllocSprintfEntry,AllocSprintfNative}, InitializedString, WriteLogObservation, Audit, PHASES, docs/lanes/bprime.md.
The inherited /tmp/sprintf-native-build7.log passed 1403 jobs, including both new modules; inspect current edits and theorem statement first.
Verify actual entry at 0x80013ec4 through original native RA, restored ABI, exact signed decimal bytes/string ownership, observable output and explicit runtime/frame assumptions. Do not assume complete primitive or C_CALL return.
Finish all-new-theorem focused audits and registrations, affected builds after rebase, generator/discipline checks and documentation. Remove experiments/syi/sprintf-entry-prefix.lean only if confirmed duplicate scratch (preserved in checkpoint commit).
Do not raise budgets, fabricate raw sailOutput equality or narrow GoodF1. General d/i/u/x/X/o flags/width/precision, major/large allocation and C_CALL2 remain open.
Done: reviewed checked decimal native summary with exact validation evidence and explicit remaining caller conditions; leave edits for lead integration, no unrelated GC work.
