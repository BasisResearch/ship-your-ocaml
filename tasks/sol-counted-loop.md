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

Target: carry the checked physical custom-count evidence through the actual F1 loop and C_CALL setup/return, so channel calls consume the successful-state Fits bound.
Start only after the current custom-count worker is checked and committed; inspect its final remaining-obligation list before editing.
Files: OCaml/Refinement.lean, Vm/Repr, Vm/Sim/{ChannelReadiness,CcallRows,F1Ccall,F1Rows,WhileMinTable} and shared row/frame producers; generator scripts for generated files.
The current CountedVmReprAt and CountedCcallSetupPost sidecars are not yet the ordinary loop invariant. Merely defining a stronger interface does not discharge the existing headline.
Choose one shared representation/frame abstraction; reuse generic rows under strengthened runtime invariants where valid rather than duplicating every opcode proof.
Before changing every row, also inspect boundary coherence in the runtime invariant plus represented refcounts as a route to deriving the physical model count; the present runtimeOk does not contain that fact.
Any such coherence field needs actual startup, call and ordinary-frame producers; an unexplained implication from the old invariant would repeat the rejected universal-budget route.
Carry physical Customs c s.world.customs from the actual startup zero witness, frame it across non-custom calls, and use CustomMemCall's ACTUAL counted return for allocations.
CustomMemCall remains the accepted named machine premise. Do not infer counts from Ready k, unconstrained CustomMemReturned, or channel refcounts during the pre-call increment.
Connect counted open/out-list summaries to the real C_CALL rows and interpreter assembly; preserve the full GoodF1 domain and accurately retain after-call runtime/pin suppliers still unproved.
Do not replace missing suppliers by assuming the desired primitive or row result. CountedResult.physical alone is not a complete ChannelCustomsRepr if that remains the boundary invariant.
Done: F1 assembly consumes per-call readiness from Fits and carried counts, focused affected builds/standard-axiom audits pass, and no count-preservation supplier is silently assumed. Document remaining runtime suppliers precisely.
Leave checked edits for lead review and integration; do not claim all F1 closed while registration, general formatting or reset/libHeap are open.
