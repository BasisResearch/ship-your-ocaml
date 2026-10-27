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

Target: lift the actual console primitive returns to the counted loop using refcount/length preservation while allowing channel buffer and offset changes.
Files: Vm/{Repr/ChannelCounts,Sim/ChannelCountFrame,Sim/CountedRuntime,Sim/ConsoleCall,Sim/F1Console,Sim/PrimConsoleReturns,Sim/CountedCcall1}.lean and related concrete output primitive return modules.
Read Chan and the actual primF1Impl/flush/output semantics. Console calls change world.chans buffers/offsets, so counted_row's whole-chans equality is not their semantic frame.
Prove a reusable ChannelCustomsRepr transport from equal channel-list length and per-id refs, plus the actual physical-state/refcount/open-link frame. Derive semantic facts from successful flush/output returns, not an assumed total-count equation alone.
Lift ConsoleStable at countedLayout using the actual consoleWindows, selected LibHeapAt/opened-list geometry, channel-record separation, and CustomMemCall.apart/accounting.frame. Account for errno words, native stack, target record payload and every other record.
Reuse generic native console return proofs and actual C_CALL setup/return adapters. Keep GoodF1 console guards and Fits; handle caml_ml_flush, caml_ml_output_char, caml_ml_output and caml_ml_output_bytes at their real arities.
No presumed counted successor, matching placement, stronger WindowStable, or new global runtime fact. Recover actual returned placement through existing opened-list coherence and physical observation frame.
Done: checked complete counted console primitive returns/consumers at supported arities, focused affected build and allowed-axiom audit, precise remaining complete-C_CALL obligations.
CustomMemCall remains named. Opening/listing, named registration, general formatting and full table assembly remain separate. Do not claim whole C_CALL opcode closure until all of its real branches compose.
Leave checked edits for lead review/integration; record failed contract routes in DEAD-ENDS.
