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

Target: compose the actual bf_allocate entry's empty-exact-slot classification with the checked nonzero larger-small-list search, allocation and native return.
Files: Vm/Gc/{BestFitMissing,BestFitSearchRoute,BestFitPreservation,BestFitNextAudit}.lean and one focused original-entry composition module if useful.
BestFitMissing.missing already runs BestFitSmall.pc=0x800073ac through the read-only size/slot probe to fallback 0x800073cc. BestFitFallback.search_allocate starts at that fallback and now has returned SmallRepresentation/AllocatedApart producers.
State a named input only over original entry observations: positive small request, empty exact-size list, original SmallRepresentation, existence of a nonempty larger list, native stack/source windows, actual code/register/return alignment. Derive the probe slot observation from SmallShape; do not assume the intermediate fallback state or final representation.
Run missing, derive SearchInput at its actual returned configuration from preserved memory/registers, then compose search_allocate. Keep both stage witnesses in a named post; transport real result/header/counter/ABI/output/log facts back to the original allocator entry.
Return SmallRepresentation and allocated-block separation for the actual selected final list family. Reuse GprsSame, LiveFrame and existing log/readback abstractions; never redo instruction proofs or normalize large nested memories wholesale.
Done: checked FnSummary from original bf_allocate entry through this complete successful next-size path, focused affected build/allowed-axiom audits, generator checks and exact remaining dispatch/producer obligations.
This handles the empty exact-size/nonempty larger-small-list case only. Exact-size cases, zero filtered bitmap/large-tree path, original caller/invariant production, full allocator readiness and collection remain explicit; BarrierGrowthFull remains G2.
Update docs/lanes/a6-gc.md and PHASES, record dead ends, leave checked edits for lead integration.
