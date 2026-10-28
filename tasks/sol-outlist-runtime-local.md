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

Target: repair and supply the listing runtime interface from the actual entry stack, selected heap and checked native return, eliminating unrestricted allocator-write framing.
Files: Sim/{OutListAdapter,OutListRun,OutListWalk,CountedChannelRows}.lean, Gc/{F1Heap,F1Runtime,CustomMem}.lean and a small checked obstruction module/audit if useful.
First check the precise current entry defect: OutListRuntime.entry quantifies over sp but receives only runtime and LoopGeometry (which does not mention sp). VmPoint includes saved slots [sp-16,sp+8*stack.length), yet the result requires all points below heapEnd. An arbitrary sp=heapEnd+16 should give a conditional interface obstruction; verify it without claiming a reachable counterexample/global inconsistency.
Replace that overstrong entry law with actual stack/data/setup requirements already supplied at out_list_entry. Derive the selected H/cap, RecordsPlaced, full CustomLedger/CustomSpace/NamedLedger, coverage and payload separation from actual LibHeapAt and LoopGeometry/data, retaining named roots and dynamic remembered storage.
OutListRuntime.runtime currently assumes arbitrary OutListWrites state H and only young_ptr bounds preserve the whole runtime; H is unconstrained. Replace it with a bounded return interface fed by the actual OutListReturned and selected input ledger. Do not assume a whole primitive result or returned LibHeapAt as the final supplier.
Reuse OutListReturned.spatial_heap/physical_records, returned refword/list facts, domain/static frame lemmas and the selected unchanged ref-table/named ledger to reconstruct actual F1 runtime fields.
Audit allocation credit: CustomMemReturned.heap carries existential cap' without a bound relating it to entry cap, whereas LibHeapAt.room retains future C-allocation reserves. Do not infer reserve from HeapReady alone. Track concrete table-allocation charge/reserve at the accepted named CustomMemCall boundary, with real startup/frame/caller producers and actual returned capacity; never insert a whole-runtime axiom.
A quiet-count/table-geometry bound may be needed to rule out later custom reallocations. Use actual custom-table shape and generated sizes; do not manufacture a capacity bound from occupancy alone or silently change GoodF1.
Keep physical Customs/read-only call-context production separate where genuinely still open; coordinate with sol-custom-physical-runtime.md. CustomMemCall remains the accepted named native allocation obligation, including explicitly documented physical spending duties.
Done: checked old-entry obstruction, repaired concrete listing entry/runtime producer (or precise remaining native spending component if the current contract cannot supply it), existing counted listing C_CALL consumers still build, focused allowed-axiom audit and accurate PHASES/lane log.
Use mandatory shared abstractions and default budgets; record failed interfaces, preserve existing real native execution results, leave checked edits for lead integration. BarrierGrowthFull remains G2; no C4 round 2 before F1.
