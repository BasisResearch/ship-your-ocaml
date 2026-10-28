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

Target: close the counted write-row spatial supplier by composing the checked barrier adapters with the selected custom-space invariant.
Prerequisites: the custom-apart local repair and counted-field-writes work must both be present; inspect their actual checked APIs before changing anything.
Files: Vm/Gc/{CustomLedger,F1Heap,F1Barrier,F1Grow}.lean, Sim/{CountedRuntime,F1Growth,BarrierF1} and the counted write rows/generator.
First prove LibHeapAt supplies RefCustomApart (or its final equivalent), without a new premise. Split h.table.shape: unallocated base is immediate; for storage, use its arena bounds for the static resource and apartBlocks for the domain resource.
For custom table/backing storage, use h.customSpace.allocated with the actual remembered-storage extent in namedBlocked chs c; preserve the real nonzero-base and extent arithmetic. Shared membership in H alone does not prove separation.
Feed this producer into fast insertion and empty-table growth count frames. Retain actual native observations and complete count placement through the same run; no backward count transport without evidence.
Return complete counted SETGLOBAL, SETFIELD/0/1/2/3 and OFFSETREF rows from real runtime suppliers. Update the exact generated partial-table/census only for fully supplied rows.
BarrierGrowthFull remains the named G2 obligation. If its old base-layout contract cannot preserve the counted invariant, retain the exact stronger full-growth boundary explicitly; do not call that a proved lift or add an arbitrary whole-row premise.
Done: the extra RefCustomApart supplier is derived from actual selected heap state, seven row contracts are checked with exact residual G2 premises, affected builds and all-new-theorem audits pass, and ledgers distinguish completed rows from open full-growth producers.
Record any real incompatibility precisely; keep GoodF1 and the physical count meaning unchanged. Leave checked edits for lead integration.
