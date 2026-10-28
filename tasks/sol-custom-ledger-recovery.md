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

Target: finish reviewable selected-custom-ledger repair inherited from the interrupted Sol worker; preserve all existing proof edits.
Read tasks/sol-custom-ledger.md for original scope, and tasks/sol-custom-apart-local.md for the queued separate obstruction; do not conflate them.
Files: Gc/{CustomLedger,CustomLedgerObstruction,CustomMem,F1Heap,F1Runtime,ChannelCustomCount,F1Grow,F1Barrier}, Channel/MlOpen and OutList consumers, Layout generator, Audit and lane docs.
The inherited affected build /tmp/custom-ledger-affected5.log passed 3628 jobs. Inspect evidence and edits before rerunning; no new code since that success unless the recovered diff says otherwise.
Finish all-new-theorem focused audits and registrations, generator checks, discipline checks and affected consumer validation after rebase. Correct only actual gaps in this selected-ledger change.
Review same existential heap/ownership, actual captured startup coverage and freshness; do not imply full physical Customs or native CustomMemCall is proved.
Keep named CustomMemCall and preserve the precise conditional empty-ledger obstruction. Global records/frame incompatibility is queued separately, not a reason to claim the named premise globally inconsistent.
Done: checked selected-ledger patch with exact audit/build evidence, updated PHASES and docs/lanes/a6-gc.md, dead ends and exact remaining producers. Leave checked edits for lead review; no further unrelated work.
