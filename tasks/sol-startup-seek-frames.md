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

Target: derive the current descriptor bytes, OpenFile/file-source observations and fd-position at ResetCodeSeekEntry from the actual reset execution, closing the precise source-frame residual before the CODE reverse scan.
Read the CODE seek entry handoff in docs/lanes/a0-boot.md and the three latest CODE dead ends. Current reset reaches 0x80004bcc with actual count/table pointer, selected descriptor ownership and fd=3/argv; it does not yet frame the descriptor contents or file/source bytes.
Files: Boot/Startup/{InitGc,InitGcReset,MinorHeapSet,MajorHeapInit,InitStackReset,AtomTable,AtomTableReset,Backtrace,BacktraceReset,InterpreterInitReset,SeekCodeReset,ReadSections*,DomainRecord,CallerFrame} and the owning lower-level initialization summaries/audits where needed.
Use LiveFrame on the selected original descriptor allocation and actual extended heap ledger; propagate it through initialization using existing allocator owned-byte contracts. Reuse LiveFrame.of_memory/of_stack/of_arena/of_foot/trans/mono; do not hand-roll universal live-block frame fields.
For embedded source/HTIF file records/fd-position and CODE literal, identify exact existing byte windows and extend the actual native summaries with selected read-only frames. The old lowKept requires x<heapStart; CallerFrame starts above the source image. Neither transports those bytes without a new actual-footprint argument.
Preserve the full reset/source ancestry and all actual nested runs. Thread concrete frames through prologue/GC/minor/major/stack/atom/root/interpreter and the read-only CODE call, deriving the selected record/table values at 0x80004bcc.
The selected loader pieces have file length 9388, CODE length 764 and reverse CODE offset 9331 (position 57). The stock ELF embed has a different program: use SeekSectionData/source image, not its stock payload. Steps alone supplies no memory frame; do not assume a later matching snapshot.
Do not duplicate generated seek segments or kernel certificates. Keep the subsequent scan as a separate bounded task unless these source producers finish early; then reuse indexedLoop, bounded strncmp (CRCS first-byte prefix!) and actual lseek/HTIF machinery to 0x80004eb0.
Done: checked concrete current-source observation producer from ResetCodeSeekEntry/actual reset with no new arbitrary post-memory/run premise, affected initialization/entry consumers and all-new-theorem audits. If a lower-level summary must be strengthened, do that work; a contract gap is not a user blocker.
Keep GoodF1 unchanged and later CODE loading/PRIM/DATA/promotion/sys/Loaded explicit. Update a0-boot/PHASES/DEAD-ENDS with precise remaining work and leave checked edits for lead review.
