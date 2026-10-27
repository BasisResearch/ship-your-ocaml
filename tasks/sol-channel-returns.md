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

Target: reconstruct complete ChannelCustomsRepr after the channel-opening and out-list calls, and retain it through the actual unary C_CALL return.
Start from the checked count bridge and counted setup/suffix checkpoint; read the worker's final remaining-obligation list before editing.
Files: OCaml/Vm/Sim/{OutListWalk,OutListRun,OutListAdapter,OpenOutPayload,OpenOutReturn,ChannelReadiness,CountedCcall1}.lean and shared channel-frame helpers.
CountedResult.physical is insufficient: the boundary needs natural refcount observations, list links and physical Customs for the SAME returned ChanPlace witness as CcallReturn.
Reuse open_out_counts for opening. Strengthen the named return record so it retains this evidence on the actual execution; do not assume a second unrelated post or a universal count implication.
For out-list, derive the real four-byte increment readbacks from the native stores, preserving unvisited/unlisted records. Track the visited portion once with a shared walk invariant, not one bespoke proof per channel.
Use the successful successor's Fits/customs bound (quietBound=5) to prove no 32-bit wrap; do not add a fresh model guard or infer physical count from the transient refcount sum.
Reuse ChannelCountFrame for the C_CALL suffix, whose generated return retains memory equality. Reconstruct counts at the final loop-head placement actually chosen by the ordinary return.
Keep existing runtime entry/after suppliers explicit, and keep CustomMemCall named with its exact machine count post. This task closes refcount/boundary producers, not every opcode's loop preservation.
Done: all three channel primitives return complete counted boundary evidence and the unary arm preserves it on the same run, focused build/standard-axiom audits and generator drift pass, with no assumed readback/no-wrap field replacing the proof.
Leave checked edits for lead review/integration and list the remaining startup and non-channel loop-preservation obligations precisely.
