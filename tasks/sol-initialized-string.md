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

Target: prove the native caml_alloc_initialized_string short/nursery summary needed by the formatter continuation.
The previous task incorrectly requested caml_copy_string. AllocSprintfLong now checks the real continuation at 0x80013f1c to 0x8000c284, with length in a0 and buffer pointer in a1; reuse it and do not repeat that rejected splice.
Files: Primitives/StringNursery.lean, StringCopy{Allocated,Finish,Readback,Observations}.lean, Memcpy.lean, new initialized-string wrapper, and its generator/step table; lane, PHASES and audits.
Generate/check the actual caml_alloc_initialized_string save, allocation-call, memcpy-call and native return boundaries with gen_fn.py/shared segment tools; verify actual ELF call targets.
Reuse alloc_string_nursery and the existing memory-copy/initialized string representation abstractions. Factor common source/frame/return laws beside existing StringCopy producers instead of duplicating their large proofs.
Its source is the caller's native stack buffer, not necessarily an OCaml heap string or static read-only data. Derive each callee input from actual prior stores and preserve source bytes across nursery allocation.
Retain explicit length/young-room/native stack/separation/runtime premises, full returned byte-string layout including padding, ABI/output and byte frames. Never assume the callee execution or final post.
For the formatter consumer the known length <=20 permits the nursery path; do not generalize that bound to arbitrary GoodF1 formats or infer it from Fits.
Done: checked entry-to-return native summary at 0x8000c284 with data-only preconditions suitable for AllocSprintfLong, affected guarded builds, focused allowed-axiom audit and generator drift checks.
If straightforward, expose its direct composition after AllocSprintfLong.short_continuation, but keep the full formatter prologue/wrapper/original-return and C_CALL2 suppliers explicitly open until proved.
Leave checked edits for lead review/commit/integration. Record new dead ends; preserve the full GoodF1 domain and standing named premises.
