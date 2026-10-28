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

Target: prove native vsnprintf entry-to-return for the LONGINT decimal call used by caml_alloc_sprintf, using the checked caller layout.
Files: OCaml/Vm/Primitives/Format/{SvfLong,VsnprintfSteps}.lean and a new wrapper module; scripts/syi/gen_snp_extra.py; stdio templates if a shared interface must change.
Reuse vsnprintf_layout: synthetic base sp+48, FILE sp-216, 128-byte caller buffer sp+16, seven varargs slots sp+184; do not recreate the old rejected geometry.
Compose generated wrapper rows with svf_entry, svf_iterLD and svf_iterEnd; prove actual FILE initialization, exact return length, truncated bytes/NUL, ABI and outside-memory preservation.
Use the existing SnpW-to-machine adequacy/native FnSummary abstraction; inspect the corresponding snprintf wrapper and avoid an assumed callee run or desired post.
A LONGINT decimal summary is an explicitly scoped milestone, not general format_int: full GoodF1 accepts d/i/u/x/X/o, flags, width and precision.
Keep the wrapper's geometry reusable for arbitrary destination/capacity where practical; the 128-byte caller is a checked instance.
Done: native wrapper summary with a non-vacuous real caller instance, focused build/audits and generator drift pass; document exact remaining alloc_sprintf and C_CALL2 obligations.
Large formatted strings can require major allocation; do not infer nursery size from Fits or weaken GoodF1. Leave checked edits for lead integration.
