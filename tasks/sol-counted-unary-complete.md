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

Target: close the complete counted C_CALL1 opcode on GoodF1 using the concrete reviewed opening/listing runtime producers, ordinary primitive returns, fresh OO ID, flush and actual native exit.
Prerequisite: selected-credit listing and opening after-runtime suppliers are reviewed and concrete at f1Layout. If a producer still has a returned-capacity/whole-runtime premise, finish its precisely identified residual before claiming whole-row closure; this packet is queued behind those tasks.
Files: Sim/{CountedChannelRows,CountedPrimRows,CountedConsoleRows,CountedControlRows,CountedCcall1,CcallExitF1} and a dedicated unary assembly module, owning census generator/audit if appropriate.
Reuse counted_supported_prim_returns/counted_supported_c_call1_next, counted_fresh_oo_id_next, counted_flush_next, counted_channel_c_call1_next, counted_c_call1_halt and counted_c_call1_row_of_next. Do not rebuild native setup/callee/suffix or exit.
Classify all actual successful unary primitive cases from primF1Impl and InF1, including wrong/missing arguments and rejected lookup cases. Existing 19-name ordinary adapter covers 16 unary names; the counter, flush and three allocating channel names have separate checked summaries. Exit has an actual halt, not a successful return.
Retain GoodF1/Fits/reachability and actual native count/returned placement through every success; rejected/error/unsupported semantic outcomes are handled by the existing OpArm outcome interface. Do not strengthen GoodF1 or assert counts from an ordinary weak setup.
Instantiate runtime producers using only named CustomMemCall and concrete physical/credit facts already supplied by the counted relation, plus existing G2 boundary. No new whole-opcode, whole-primitive, generic arbitrary-H write or returned-runtime assumption.
Avoid import cycles with CountedControlRows: place complete success classification/assembly below the census, retaining the existing shared native halt helper or factoring it into a small lower module without changing proofs.
Done: audited complete counted C_CALL1, census 133/134 with only C_CALL2 remaining, affected counted/F1/entry consumers checked. Document every retained named premise and leave checked edits for lead integration.
