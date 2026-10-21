Binding rules: read CLAUDE.md, PHASES.md, PLAN.md and your lane log; user directions override older briefs.
Run scripts/abs_inventory.sh before proof work; reuse mandatory abstractions by name.
No sorry, axiom, native_decide, bv_decide, heartbeat increases, or edits to generated outputs.
Edit generators; audit new theorems with only propext, Classical.choice, Quot.sound.
Before each build check free -g (available >=25 GB); one build per worktree.
Run all Lean through systemd-run --user --scope -q -p MemoryMax=12G env LEAN_NUM_THREADS=2.
Do not add ulimit -v: virtual reservation breaks the large import closure; the cgroup enforces 12 GB.
Work only in this worktree; preserve inherited WIP and never force-push or reset it away.
BarrierGrowthFull stays with G2; CustomMemCall remains a named premise; C4 round 2 waits for F1.
Read docs/lanes/DEAD-ENDS.md before choosing a route; record newly refuted routes there.
Build affected modules; register audits and update lane log/PHASES accurately; commit small checked steps.
Land only via scripts/integrate.sh (full gate and serialized fast-forward push); never bypass a failed gate.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: validate and land the recovered reset-through-atom-table milestone.
Files: OCaml/Vm/Boot/Startup/{AtomTableReset,AtomTable,InitStackReset,InitGc,MajorHeap}.lean; OCaml/Audit.lean; PHASES.md; docs/lanes/a0-boot.md.
Read the lane log and predecessor commits; preserve all existing startup work.
The new reset_init_atom_table_returned_exists already built and the full Audit build passed.
First inspect /tmp/syo-startup-audit.log and audit the exact reset theorem premises, then run the full integration gate.
Resolve routine rebase or gate failures without weakening invariants or claiming the complete reset-to-cut result.
Done: predecessor startup commits and the new reset-to-atom theorem land via scripts/integrate.sh with standard axioms.
Record remaining reset-to-cut/libHeap steps precisely in the lane log.
