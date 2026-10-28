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

Target: discharge the numeric reserve seam in outList_f1_restore by carrying actual selected custom credit through the runtime invariant and each native listing call, relative only to the accepted named CustomMemCall.
Prerequisite: reviewed OutListF1/OutListF1Runtime/CustomMemCredit and the latest physical-custom/read-context handoff. Read both lane entries before editing. Do not overlap the active physical-custom worker.
Files: Gc/{F1Heap,F1Runtime,CustomMem,CustomMemCredit,CustomLedger}, Primitives/Channel/{MlOpen,OutList*}, Sim/{OutListAdapter,OutListF1,OutListF1Runtime,CountedRuntime,CountedChannelRows} and their affected actual callers/audits.
Use the existing extra reserve customTableReserve (1 MiB only while base=0), startup selected producer, ordinary credit frames and CustomMemSpending.trans/room. Integrate the reserve into the actual selected runtime heap invariant; an extra assumption at the whole primitive is not closure.
Keep dependencies low: move shared charge/reserve and native credit/spending types below CustomMem/F1Runtime where needed rather than creating an import cycle. Preserve existing interfaces by honest projections where possible.
Refine the accepted CustomMemCall with concrete input-credit/read-context and actual returned spending evidence. The credited return must use one selected H'/cap' with HeapReady, full ownership/ledger, retained blocks and cap + reserve(after) <= cap' + reserve(before). Do not pair a capacity law with an unrelated existential heap or infer positive credit from HeapReady alone.
Retain the actual first request 792576 and checked vsaChg; later no-growth spending needs real QuietCustomTable/physical-count pins, not occupancy alone. The native allocation execution and this precise spending contract remain within named CustomMemCall, not an added whole-listing runtime/LibHeapAt premise.
Produce stronger credit at the cut and preserve it through all affected ordinary/count/setup/native-safe frames. If old interface-obstruction lemmas refer to the now-repaired invariant, restate their old numeric/structural premise explicitly; do not silently erase the dead end or claim the old counterexample refutes the strengthened contract.
Thread selected capacities through the real OutList walk and calls, compose spending and existing frames on actual intermediate states, and feed the resulting ordinary reserve to outList_f1_restore on that same returned ledger.
Opening shares the native custom input: preserve its real 65616-byte record spending and recordCharge reserve decrement in affected consumers. Full OpenOutRuntimeAt.after reconstruction remains the separate opening packet unless already supplied.
Done: checked concrete OutListRuntime at f1Layout relative to named CustomMemCall with actual credit producers and return propagation, affected counted/F1/entry consumers and all-new-theorem audits. If another concrete seam remains, state it exactly; do not label an assumed returned capacity or runtime as a producer.
Keep GoodF1 unchanged, BarrierGrowthFull with G2 and C4 round 2 waiting. Update PHASES/lane log/DEAD-ENDS and leave checked edits for lead integration.
