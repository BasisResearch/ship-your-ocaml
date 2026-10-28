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

Target: compose the already checked ordinary/read-only and allocating primitive summaries through actual counted C_CALL1/2 success paths, supplying entry counts explicitly.
Files: Vm/Sim/{ChannelReadiness,CountedCcall1,CountedCcallSetup,CountedChannelRows,CountedPrimAllocRows,PrimConstReturns,PrimStringEqualReturns,PrimStringNotequalReturns}.lean and new shared adapters/generators.
Reuse counted_memoryStable, counted_runtimeFrame, counted_allocFrame and counted_primAllocFrame with the existing native primitive return contracts; do not reprove their instruction runs.
Interface inspection: CountedPrimReturnsAtR currently receives ordinary CcallReady at the loop entry, without counts. Counts enter only the later CountedCcallCallee.summary. A local countedLayout PrimReturnsAt cannot be instantiated at that original entry without its carried count witness.
Introduce one named counted entry/return interface or explicit entry-count argument supplied by CcallReady.of_counted_loop. Adapt existing channel returns by forgetting that extra input; do not assume counts from ordinary runtimeOk or infer the original counts backwards from a callee post.
Produce complete counted callee posts at the actual returned channel placement, using linked-list/geometry coherence and the real unchanged-channel semantics. Preserve the original reach/Fits/successor/heap/arity guards; prove all local-layout retargeting facts.
Instantiate 19 names: nine Sys constants, string/bytes length, string equality/inequality, sys_argv, int_compare, three allocating Sys returns and int64_float_of_bits (using its existing AllocFrame contract). Record exact supported names and arities from primF1Impl rather than assuming all 30 F1 primitives are unary.
Compose real dispatch/setup/callee/suffix runs: reuse counted_c_call1_success, and generate/factor the C_CALL2 counted setup/suffix using existing native rows and actual write logs. Add no arbitrary poststate or complete counted-OpArm supplier.
Done: checked actual C_CALL1/2 success for those names, focused affected builds/allowed-axiom audits, generator checks and updated exact remaining primitive/opcode census. Existing channel successes must still check.
Console effects, channel opening/listing suppliers, formatter, named registration, fresh_oo_id counter effects, exits and full C_CALL1-5/table coverage remain separate unless their actual existing proofs suffice. Do not claim whole opcode closure from successful named cases.
Keep the entry-count interface reusable for further arities; record interface dead ends and leave checked edits for lead review/integration.
