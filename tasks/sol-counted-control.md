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

Target: finish the ordinary counted memory/control rows that reuse the existing counted MemoryStable and RuntimeFrame, leaving allocation/barrier/new native-effect frames to their separate tasks.
Files: Vm/Sim/{CountedRuntime,CountedMemoryRows,CountedStackRows,A2TableRows,ControlRows,OperandTableRows,SignalRows,SwitchRows,StopRow}.lean and counted row generator/audit.
Reuse counted_row/counted_memory_row/counted_stack_row and the generic checked native rows. Do not duplicate instruction execution or add a new preservation premise.
Cover remaining constants/atoms, integer arithmetic/comparisons/branches/SWITCH, APPLY/APPTERM/RETURN/RESTART, CHECK_SIGNALS and STOP wherever the existing proved frames suffice.
Preserve GoodF1/Fits/capacity, ExtraBounded and integer/arity/branch guards through their actual existing suppliers. STOP must retain the real exit facts from the entry runtime, with no successor count requirement for a halt.
Derive unchanged channel semantics from actual stepI, using the authoritative opcode operand counts before unfolding; read the counted-stack heartbeat dead end. Factor shared helpers for apply/tailcall/return semantic operations rather than expanding them repeatedly.
DIVINT/MODINT require their caught-raise path; include them only if the actual RaiseRuntimeFrame lift is proved from existing count frames. OFFSETREF writes an object: do not treat it as memory-preserving or stack-only.
Done: checked supported counted OpArm instances and exact remaining opcode census against opF1, focused affected builds and allowed-axiom audit, generator/discipline checks and updated lane ledger.
Do not change GoodF1, weaken counted invariants or claim full table closure. Allocating/barrier rows, effectful C_CALLs and any newly required runtime-frame supplier remain explicit.
Leave checked edits for lead review/integration.
