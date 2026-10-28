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

Target: extend the actual reset prefix from InterpreterInitReset's debugger return through the CODE section seek, ending at caml_main 0x80004eb0 with the real section length and fd position.
Prerequisite: the checked interpreter/debugger initialization result is on main. Files: Boot/Startup/{InterpreterInitReset,ReadSectionsLoop,OpenFile,Strncmp*,Seek*} and scripts/gen_startup_rows.py; add bounded native seek modules as needed.
The pinned ELF calls caml_seek_optional_section directly at 0x80004ea4 (entry 0x80004bcc, return 0x80004ea8); the missing-section branch at 0x80004eac must actually be ruled out. Do not call an imagined separate caml_seek_section wrapper.
Generate the native blocks and literal CODE name certificate from the ELF. Reuse existing strncmp summaries, lseek/HTIF seek summaries, FnSummary call composition and indexedLoop for the reverse descriptor scan.
The scan starts with 16+8*num_sections, adds each unsigned descriptor length, compares exactly four name bytes, and on success performs lseek(fd,-ofs,SEEK_END) before returning the signed descriptor length. Track the actual modular arithmetic and its bounds.
ReadSectionsDone already supplies seven swapped descriptors, the table pointer and num_sections, OpenFile, embedded source and fd position. InterpreterInitReset retains the actual ancestor and Steps, but these alone do not frame its memory into the new call.
Derive the required table/trailer/file observations through the executed GC/stack/atom/backtrace/interpreter summaries using selected LiveFrame, CallerFrame, domain/static windows and existing heap-ledger inclusion. Do not assume an arbitrary final memory match or attach the old observations to the new state without a proof.
Expose a named concrete seek input/output and reuse it for the checked CODE lookup. Retain the selected heap/capacity, fd=3/argv ABI, descriptor ownership, source-image witnesses and actual updated fd position.
Done: a universal parsed-ELF-reset-to-CODE-seek theorem with actual Steps and precise next PC, checked generated blocks and all-new-theorem audits; update PHASES and a0-boot log. If a source frame is missing, prove that bounded frame component before claiming the reset continuation.
Code allocation/read, code-fragment registration/MD5, primitive table, DATA unmarshalling, promotion, sys/argv and Loaded remain later work. Captured memory is not reset execution.
Record failed routes; retain GoodF1 and the named G2/CustomMemCall boundaries unchanged. Leave checked edits for lead review/integration.
