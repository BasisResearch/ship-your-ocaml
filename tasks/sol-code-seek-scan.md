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

Target: execute the real optional-section reverse scan from ResetCodeSeekEntry to caml_main 0x80004eb0, returning CODE length 764 and fd-3 position 57.
Prerequisite: reviewed source-frame handoff. Reuse ResetCodeSeekEntry.observations/CodeSeekSourceObserved; descriptor bytes, OpenFile, EmbedImage, fd position and CODE literal now come from actual reset execution, not an extra later-memory premise.
Files: Boot/Startup/{SeekCodeReset,SeekCodeCall,SeekOptional*,SeekSectionData,Strncmp*,OpenFile,Seek*}, scripts/gen_startup_rows.py and focused audits. Read the latest a0-boot and DEAD-ENDS entries first.
The actual call enters 0x80004bcc, returns 0x80004ea8, then code_seek_present rules out the missing-section edge to 0x80004eb0. Retain reset/source ancestry, selected H/capacity, descriptor ownership and fd/argv ABI.
Reuse already generated optional-seek blocks and CODE literal/data certificates; do not regenerate or reprove their arithmetic unless a specific missing observation requires it. Compose with FnSummary, indexedLoop, existing strncmp and lseek/HTIF summaries.
Start offset 72; the real reverse lengths produce [72,123,407,709,8567,8567,8567,9331]. Track both unsigned accumulation and signed return length; success performs lseek(fd,-9331,SEEK_END) on the selected 9388-byte image, giving 57.
Compare exactly four name bytes. CRCS and CODE share their first byte; reuse seek_crcs_common_prefix and actual second-byte mismatch, not a false first-byte test. The stock ELF embedded CODE is a different image and must not supply these observations.
Use named scan input/invariant/output structures and actual native memory/ABI frame evidence. Preserve source records/descriptors across scratch stores and syscalls via existing LiveFrame/CallerFrame/window abstractions; do not infer memory equality merely from Steps.
Done: universal parsed-ELF-reset-to-completed-CODE-seek theorem with actual Steps, precise PC, return length and updated file position; affected startup build, all-new-theorem focused audit and honest PHASES/a0-boot/DEAD-ENDS updates.
CODE allocation/read, code-fragment/MD5, PRIM, DATA, promotion and system/argv remain later work. Captured image certificates are not execution. Keep GoodF1 and named G2/CustomMemCall boundaries unchanged; leave checked edits for lead review.
