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

Target: finish the inherited formatter caller-layout generalization needed for vsnprintf in caml_format_int.
Files: experiments/syi/stdio-template/{SnpCtx,SnpPrint,SnpSvf,SnpSvfConv,SnpSvfLoop}.lean (locate actual subpaths); scripts/retarget_stdio_specs.py; OCaml/Vm/Primitives/Format/SvfLong.lean; docs/lanes/bprime.md.
The preserved WIP directly edits generated VsaIris/Vsa/Snp*.lean outputs: first migrate those changes into the templates and regenerate, retaining the same intended proof changes.
Read bprime's format status around lines 128-171; the old SnpGeom excludes the real vsnprintf buffer and vararg layout.
Reuse the existing LONGINT proof and stdio battery; generalize frame/buffer/va_list ownership rather than assume a run or add impossible placement premises.
Done: existing SnpFmt and Format.SvfLong consumers build at default proof budgets, and the generalized interface admits the concrete vsnprintf layout; audit changed public theorems and pass template drift.
Record the precise remaining wrapper/caml_alloc_sprintf/C_CALL2 obligations. Current formatInteger accepts d/i/u/x/X/o plus flags/width/precision; a %d-only summary cannot close the general GoodF1 field. Do not begin C4 scale-up.
Leave checked edits for lead review; do not attempt sandboxed Git writes or integration.
