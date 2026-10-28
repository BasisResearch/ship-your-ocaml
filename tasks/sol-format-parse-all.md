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

Target: close the native parse_format call for the full formatInteger input grammar, including l/n/L annotations, and supply the real caml_format_int caller prefix up to caml_alloc_sprintf.
Files: Primitives/Format/{ParseFormatCall,FormatInt,ParseFormat}.lean, scripts/syi/ocaml_format.py, Bytecode/Data.lean only for reusable semantic lemmas, and focused audits.
The landed parse_format_call handles only the unannotated branch (prev guard). formatInteger accepts a penultimate l/n/L; native ints.c:144-185 compresses that annotation before inserting the pinned architecture suffix l.
Reuse measure/copy/append/finish, their saved bank and checked memmove summaries. Generate the missing bounded annotation branch through gen_fn/ocaml_format; never hand-edit the generated modules.
State one named returned format observation with actual output length, prefix, l suffix, conversion and NUL, original return/ABI/output/memory frame. Preserve the old plain API as a projection/instance.
Derive grammar/length/conversion conditions from formatInteger fmt n = some bytes, without evaluating a huge replicate or adding stricter GoodF1 guards. The actual copied buffer is 32 bytes; supported input has length+2<32.
Compose the existing caml_format_int entry, real parse call and signed/unsigned setup to the actual alloc_sprintf entry. Supply original saved registers and format bytes there; do not assume a parser or formatting return.
For d/i use Long_val; for u/x/X/o use Unsigned_long_val (n.toNat for a 63-bit semantic int). The unsigned bridge was already reviewed; do not resend a sign-extension counterexample to the wrong branch.
Use named contracts, FnSummary/call composition, GprsSame and LogWindows/LiveFrame; keep caller/runtime/data/nursery geometry explicit and derive intermediate observations from actual logs.
Done: full grammar native parser and original caml_format_int-to-alloc_sprintf prefix, affected/default-budget builds, all-new-theorem allowed-axiom audit and generator drift checks; precise remaining formatting/return/runtime suppliers.
This does not close general printf integer conversions, flags/width/precision, large-result allocation or complete C_CALL2. The plain decimal AllocSprintfNative.native_return remains reusable but cannot discharge those cases.
Record dead ends and leave checked edits for lead integration. No C4 scale-up, GoodF1 narrowing or native return assumption.
