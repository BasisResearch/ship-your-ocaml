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

Target: extend the checked reset-to-completed-CODE-seek handoff through actual CODE allocation/read to the caml_register_code_fragment entry, retaining selected ownership and current bytecode bytes.
Prerequisite: reviewed SeekCode/SeekOptional handoff at caml_main 0x80004eb0, length 764 and fd 3 position 57. This follows the next G2 small-wrapper rotation.
Files: Boot/Startup (new code-load module/rows), scripts/gen_startup_rows.py and layout/image generators as needed, selected WhileMinImage facts and audits.
Read the pinned disassembly and fix_code.c: caml_load_code starts at 0x80004340, calls caml_stat_alloc at 0x80004364, read at 0x8000437c, and tail-jumps from 0x800043b0 to caml_register_code_fragment at 0x8002ae4c after restoring its caller frame.
Generate the caml_main call prefix and missing load-code blocks/call shapes. Use the existing StatChecked allocation summary and ReadFile.read_file, whose count/position are already general; do not reprove malloc, memcpy or fd transport.
Derive the original inputs from ResetCodeSeekDone. Store the actual caml_code_size/start_code words, allocate the actual 764-byte owned block with a justified vsaChg/capacity decrement, read 764 bytes from selected file offset 57 and prove fd position 821.
Supply exact loaded bytes from the selected WhileMinImage CODE data, not stock c/ocamlrun's embedded program (its CODE length differs). Keep this source ancestry universal over the existing matching-ELF reset premise; no later-memory matching or assumed read-run premises.
Use LiveFrame for old selected blocks and GprsSame/CallerFrame for caller registers/saves, LogInW/LogWindows for stores, and the existing HTIF/EmbedImage/OpenFile observations. Prove copied fresh-byte ownership separately from metadata/native-write separation.
At the real code-fragment entry return actual a0=allocated code, a1=code+764, a2=1 (DIGEST_NOW), a3=0, original RA/SP, runtime/capacity, code global readbacks, fd/file/source observations and actual reset run.
Do not assume code-fragment registration or digest execution. The pinned load-code function tail-jumps directly to registration; its full return remains open until that callee is supplied. Do not insert a fictitious standalone caml_init_code_fragments call.
Done: checked reset-through-CODE-read producer to the actual registration entry, ownership/frame post, affected startup consumers and all-new-theorem audit; generator/ELF drift checks; precise next digest/fragment continuation in lane log/PHASES.
Keep GoodF1 unchanged, CustomMemCall named, BarrierGrowthFull with G2 and C4 round 2 waiting. Leave checked edits for lead review and integration.
