Binding rules: read CLAUDE.md and relevant PHASES.md, PLAN.md and lane-log sections; user directions override older briefs.
Run scripts/abs_inventory.sh before proof work; reuse mandatory abstractions by name.
No sorry, axiom, native_decide, bv_decide, heartbeat increases, or edits to generated outputs.
Edit generators; audit new theorems with only propext, Classical.choice, Quot.sound.
Before each build check free -g (available >=25 GB); one build per worktree.
The launcher encloses this worker and all builds in systemd MemoryMax=12G, LEAN_NUM_THREADS=2.
Run Lean with scripts/lean-capped.sh lake ...; it uses the inherited cap or creates a 12 GB scope.
Do not add ulimit -v: virtual reservation breaks the large import closure; the cgroup enforces 12 GB.
Work only in this worktree; preserve inherited WIP and never force-push or reset it away.
BarrierGrowthFull stays with G2; CustomMemCall remains a named premise; C4 round 2 waits for F1.
Read docs/lanes/DEAD-ENDS.md before choosing a route; record newly refuted routes there.
Build affected modules and a focused #print axioms file; register audits, but leave full OCaml.Audit to the lead gate.
Update lane log/PHASES accurately; leave checked edits for lead review.
The lead commits and lands via scripts/integrate.sh; this sandbox makes Git metadata and the landing queue read-only.
Keep reads targeted (rg, bounded sed); do not scan home or print whole huge ledgers or audit logs.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: complete the preserved physical named-node invariant migration so the OCaml consumers build without new GoodF1 restrictions.
Files: the dirty-checkpoint changes in OCaml/{Refinement.lean,Vm/{Repr,Sim,Primitives,Gc,Boot}}; docs/lanes/a1-prims.md and DEAD-ENDS.md.
The previous worker stopped on a usage limit, not a mathematical blockage. Its latest log is /tmp/syo-sol-named-geometry-launch.log.
First fix the focused errors in /tmp/a1-named-physical-build.log: WhileMinCaller and NamedOwnership; read the actual current source before applying fixes.
Continue the existing NamedOwned, stronger StackGeometry, LogWindows.named and LoadedAt.named work; do not restart it or discard WIP.
Supply matching live-malloc ownership and custom-state separation through the represented/runtime invariant and producers; fixed f1Covered extents do not cover dynamic named nodes.
HeapReady H permits a selected live-block list, so do not invent universal named ownership for arbitrary H. Track the matching witness used by the actual allocation.
Build focused producers before consumers, then the complete OCaml target. If a build has already failed, stop its remaining jobs before retrying; keep one build at a time.
Done: the complete named representation/geometry/payload consumer migration builds and focused audits pass; remaining primitive-machine obligations are explicitly distinguished.
Preserve the old-geometry alias witness as history, never as a reason to weaken the strengthened invariant. Do not stop merely because another ownership supplier needs implementation.
