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

Target: compose the real caml_alloc_sprintf native return for the plain LONGINT decimal path using the checked vsnprintf wrapper.
Start from the checked VsnprintfLong, InitializedString and AllocSprintfLong.short_initialized contracts. The last theorem already reaches 0x80013f20 from 0x80013f10; reuse that run.
Files: OCaml/Vm/Primitives/Format/{AllocSprintf,AllocSprintfLong,VsnprintfLong,ParseFormatCall,FormatInt}.lean and InitializedString.lean; generators own generated files.
Use the actual prologue/call/fits/copy/return segments and FnSummary call combinators; derive VsnLongEntry and SymbolicInput from the prologue at 0x80013ec4 and the real caller offsets. Restore saved registers and return through the actual 0x80013f20 epilogue.
Keep the parsed format outside the owned vararg window. The seven spill slots end at sp+240; the real parsed-format buffer starts there. Reuse the corrected snpAbove=192.
For signed 64-bit decimal, derive output length <=20, fit in the 128-byte local buffer, and use the actual caml_alloc_initialized_string target (0x8000c284) and nursery allocation proof. Do not assume its return or a primitive summary.
Produce the returned OCaml byte-string representation, exact decimal bytes and length, tagged/native ABI, output and memory/frame facts needed by a future C_CALL2 producer.
Carry actual allocator/runtime preconditions and selected ownership through the same run; never infer a raw sailOutput vector equality from observable-output equality.
Done: checked entry-to-return native summary for this decimal path, focused affected build/standard-axiom audits and generator checks; accurately record unsupplied caller/runtime conditions.
This milestone does not close general caml_format_int: d/i/u/x/X/o with flags, width, precision and large/major allocation remain required by GoodF1. Do not narrow GoodF1 or hide those cases.
Update docs/lanes/bprime.md (the formatting lane), PHASES and new dead ends; leave checked edits for lead review/integration. This slot is reused from G2; do not resume unrelated GC work.
