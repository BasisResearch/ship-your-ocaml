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

Target: extend the checked counted-runtime reuse to actual stack-writing F1 opcode families by proving the lifted RuntimeFrame and its concrete row instances.
Start only after the counted-loop continuation is checked and committed; read its final remaining-obligation list. Preserve countedLayout, placement coherence and the real C_CALL producers.
Files: Vm/Sim/{CountedRuntime,CountedInvariant,ChannelCountFrame,StackRows,PushRows,PushLoadRows,Assign,PushtrapRows} and actual generated row sources; use rg for current module names.
Inspect RuntimeFrame's fields and concrete f1_runtimeFrame before choosing the shared lift. Carry complete ChannelCustomsRepr, not just physical Customs.
Derive fixed channel-address bounds/separation from the entry's actual represented geometry and LibHeapAt ledger, using opened-list uniqueness for matching placements. A pure frozen footprint parameter is acceptable only when supplied from that entry.
Prove physical-state, refcount and next-link observations survive the actual VM/native stack and allowed domain-field writes. Reuse CustomMemCall.accounting.frame, ChannelCountFrame and existing write-window/log machinery.
Do not assume a counted row result, unexplained WindowStable for the stronger runtime, a matching returned placement, or new global runtime coherence. Every lift premise must have its real entry producer.
Reuse the generic stack-writing native row proofs at countedLayout instead of duplicating their instruction execution. Populate the existing PUSH/PUSHACC and stack-load/assignment families supported by this frame; handle traps only where the same proved frame suffices.
Retain actual budget, reachability and geometry guards. Do not alter GoodF1 or silently include allocation/barrier effects in a stack-only frame.
Done: checked shared counted RuntimeFrame plus concrete stack-writing row-family instances, focused affected builds/standard-axiom audit, generator checks and a precise remaining counted-opcode list.
Allocation/barrier rows, other effectful primitives, full F1Arms assembly and concrete opening/listing runtime suppliers remain explicit until proved. CustomMemCall stays named; leave checked edits for lead integration.
