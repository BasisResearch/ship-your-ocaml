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

Target: supply counted caml_fresh_oo_id success and the actual C_CALL1 caml_sys_exit halt from the existing native summaries, with no extra runtime supplier.
Files: Sim/{PrimFreshOoId,PrimSysExitReturns,CcallExitF1,CountedPrimAdapter,CountedPrimRows,CountedControlRows,ChannelCountFrame,CountedRuntime} and their owning generators.
For fresh_oo_id, the semantic world changes only ooId, hence channels remain equal. Derive counted counterWindows stability from the original counted invariant, actual counter address, selected heap/custom ownership and physical count frame. Reuse prim_caml_fresh_oo_id_returns and the explicit original-entry count witness, then recover the actual returned placement.
For exit, there is no successor counted state: project the actual counted loop to the base loop and reuse ccall1Exit_pinned with Fits, native headroom, saved registers and existing exit globals. Prove a reusable counted halt row/branch compatible with the final counted C_CALL1 OpArm.
Keep the success versus halt distinction precise: prim_caml_sys_exit_returns only excludes successful returns; it does not itself execute the halt. Cover actual unary integer argument and OS result branches through existing checked model lemmas.
If factoring a relation-forgetting helper, use the existing CountedLoopAt projections and OpArm/ArmSim interfaces; do not invent a successor placement or strengthen GoodF1.
Done: checked counted fresh-OO-ID original-entry C_CALL1 success and native sys_exit halt branch, generated exact primitive remainder updated, affected modules and focused all-new-theorem audit. Complete C_CALL1 remains open until opening/listing/named and all other remaining cases compose.
Do not change the accepted CustomMemCall or counted BarrierGrowthFull boundary. Update PHASES/lane log and DEAD-ENDS, leave checked edits for lead review/integration.
