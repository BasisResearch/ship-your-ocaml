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

Target: replace the universal open-channel readiness obligation with readiness proved at a reachable successful C_CALL from Fits and represented custom counts.
Resume preserved WIP after lead review (logs/sol-a1-prims-next-20261027-190758-*.log in main); the lead stopped the worker, not a quota or memory failure.
First replace CustomMemCall.Accounting.step: CustomMemReturned leaves state/counter bytes unconstrained, so the count guarantee must be in the ACTUAL FnSummary call post, not a universal implication from the weak returned record.
Carry that stronger return evidence through OpenedOut/out-list calls; a forgetful projection may retain old clients. Preserve the useful ChannelRefs, Repr.ChannelCounts and ChannelReadiness WIP.
Files: OCaml/Vm/Gc/{ChannelRefs,CustomMem,F1Runtime}.lean; OCaml/Vm/Repr; OCaml/Vm/Sim/{PrimOpenOutReturns,OpenOutReturn,OutListRun}.lean and their direct consumers.
Start from the landed RefcountSumAt transport/increment lemmas and ReadyOf; inspect current producers before modifying invariant fields.
OpenOutRuntimeAt.budget over every runtimeOk configuration is the recorded dead end. Supply per-call readiness using the successful successor state's custom bound and the represented refcount total.
CustomMemCall stays the accepted named machine premise; state any required exact counter transition explicitly within that obligation, never derive it from Ready k alone.
Carry the physical custom-count witness through the invariant and actual startup/channel producers; preserve the named-node ledger work and full GoodF1 domain.
io.c increments the channel refcount before caml_alloc_custom_mem; tie refcounts to physical custom accounting at VM boundaries and handle that intermediate offset. Do not define frame-stable Ready directly as the refcount sum.
Use named structures and shared framing lemmas rather than separate per-consumer byte arguments. Keep out_channels_list accounting consistent with its multiple custom allocations.
Done: the readiness bridge and its C_CALL callers build and audit, old impossible universal budget field is removed or replaced, and every still-open runtime/counter supplier is listed accurately.
Do not claim the whole openOutRuntime/outListRuntime suppliers closed unless their after-call pins and all representation producers are supplied. Leave checked edits for lead integration.
