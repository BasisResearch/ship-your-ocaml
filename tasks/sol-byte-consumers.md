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

Target: close the full-gate regression from generalizing CStr/strcmp to the full byte range.
Files: OCaml/Vm/Primitives/Uncaught/FatalNames.lean; the Vsa comparison modules/templates only if another genuine consumer needs repair; OCaml/Audit.lean; docs/lanes/a0-lib.md.
The prior complete gate has exactly one failure, FatalNames.lean:61, in .check-build.log: an old <128 proof is passed where the generalized constructor asks for <256.
Preserve the all-byte CStr contract; adapt the consumer's bound, and search for any other stale ASCII-specific use.
Build FatalNames and StrcmpSpecCond first, and run a focused axiom audit for changed declarations; the lead reruns the full gate after review.
Done: affected consumers compile, source/template drift passes, no domain restriction or proof-budget increase, and the independent byte-string change is ready for landing.
Leave checked edits for the lead; do not modify unrelated named-value representation files.
