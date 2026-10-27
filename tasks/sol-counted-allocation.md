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

Target: lift nursery/native-allocation frames to countedLayout and reuse the generic allocating opcode rows while preserving physical Customs, channel refcounts and opened-list links.
Files: Vm/Sim/{CountedRuntime,ChannelCountFrame,MakeblockRows,PrimAllocFrame,ClosureAllocRows,ClosurerecAllocRows,GrabAllocRows,F1Table}.lean and small counted allocation modules/generator/audit.
Start from the checked counted-stack frame. Reuse counted_row, counted_runtimeFrame, actual LibHeapAt ownership and opened-list uniqueness; do not duplicate native instruction proofs.
Prove counted AllocFrame and PrimAllocFrame using actual logs and nursery geometry. Derive custom-state separation from CustomMemCall.apart and count preservation from accounting.frame. Keep record/link/head words via the selected physical ledger.
A strengthened local runtime may freeze cp/world, but every frame premise needs the entry's existing producer. Do not assume WindowStable/AllocationRuntime for the stronger predicate or a counted successor as a new supplier.
Instantiate MAKEBLOCK/MAKEBLOCK1/2/3, CLOSURE/CLOSUREREC and GRAB with existing GoodF1/Fits/capacity guards, deriving unchanged channel semantics from actual stepI branches.
Check use sites of PrimAllocFrame and expose the counted instance for later C_CALL consumers; only instantiate primitive rows when all other required runtime frames already have real producers.
Done: checked counted allocation frames and supported allocating opcode rows, focused affected build and allowed-axiom audit, generator/discipline checks, precise remaining counted-row/C_CALL obligations.
Barrier growth, allocation that may trigger GC, effectful channel calls, full F1 table and concrete runtime suppliers stay explicit. CustomMemCall remains named; do not change GoodF1 or expand its nursery allocation domain.
Record any failed contract route in DEAD-ENDS and leave checked edits for lead review/integration.
