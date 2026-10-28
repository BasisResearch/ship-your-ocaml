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

Target: produce counted field-write/barrier frames and the seven remaining field-writing opcode rows: SETGLOBAL, SETFIELD/0/1/2/3 and OFFSETREF.
Files: Vm/Sim/{CountedRuntime,HeapRows,BarrierRows,BarrierF1,F1BarrierRuntime,F1GrowthPaths,BarrierKeep}.lean, Gc/{F1Heap,F1Barrier,F1Grow}.lean and a shared counted row generator/audit.
Reuse ordinary native runs, counted_row and the selected-ledger/custom spatial invariants. Derive channel reference/link and physical custom-state frames from the actual field, native-stack, remembered-table and allocator effects. OFFSETREF writes an object field, not a stack-only or memory-preserving path.
Produce local counted FieldWriteReady and BarrierRuntime, including their actual table/insertion windows. Reuse FieldWriteOk.of_geometry, F1HeapSafe and the entry's selected ledger for separation; do not assume a counted runtime successor or a new arbitrary WindowStable predicate.
Compose existing fast and initially-unallocated remembered-set growth paths with real low-level allocator/live-block frames, including the custom-state ownership now carried in LibHeapAt. Any layout generalization must preserve budget/geometry/placement and all native runtime fields.
BarrierGrowthFull remains the standing named G2 obligation. Do not silently use a base-layout proof as a counted-layout proof: derive the extra count frame from its actual native post where available, or state precisely the stronger instantiation G2 must supply. Document that boundary explicitly; do not invent an additional opaque whole-row premise.
Generate mechanical opcode wrappers and real stepI channel-preservation facts; preserve existing GoodF1/Fits/field/live-root and arity guards. Keep all allocating/ordinary rows checking after shared frame changes.
Coordination: the parallel custom-apart lane is adding LibHeapAt.customSpace : CustomSpace (namedBlocked chs c) c, including dynamic remembered storage. If this is not in your baseline, record the exact RefCustomApart gap; after it lands derive the separation from that invariant rather than keep an extra arbitrary spatial premise.
Done: checked counted field-write and barrier instances with their precise G2 boundary, focused affected builds/allowed-axiom audit, generators and exact remaining opcode census. Record any missing actual supplier rather than claiming table closure.
Update the A1 lane log, PHASES and dead ends; leave checked edits for lead review/integration.
