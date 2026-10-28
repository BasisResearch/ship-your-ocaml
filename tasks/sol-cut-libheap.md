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

Target: discharge Boot.WhileMin.cut_heapReady_covers_Statement Gc.f1Covered [(Gc.refTable, 56)] at the existing captured cut using kernel-checked memory certificates.
Files: OCaml/Vm/Boot/{WhileMinHeapChunks,WhileMinRuntime,WhileMinImage}.lean, Boot/Startup/{HeapReady,HeapFrame}.lean, a new cut allocator certificate and its generator; Gc/F1Runtime consumers.
This statement concerns the captured configuration and does not itself claim reset execution. Keep reset-to-cut/Loaded reachability explicitly open.
Inspect all HeapReady / vsaRoomB / PHeapAt / BlockHeapAt / HeapAt fields before choosing the certificate; isolated in-use header reads do not prove the complete allocator shape.
Use the checked observedMem/store-log and fillZero transport. Extract the actual chunk walk, top/break, bin chains and allocator globals from the existing capture, with bounded certificate parts checked by Lean.
Reuse ChunkWalk and BinChain transport, starts_inuseBlocks, ImgOn and existing allocator abstractions. No native validation output may be a proof assumption; do not make broad monolithic decide checks.
Choose a live-block ledger covering every f1Covered extent while retaining (refTable, 56) verbatim; derive actual size/in-use/coverage/disjointness facts rather than guessing requests from payload sizes.
Prove capacity >=2^24 from the actual top and vsaRoomB's 2*k+extendSlack bound, plus allocator text, published Caml_state and poolZero.
If the captured shape refutes an invariant field, preserve the precise checked counterexample and record the obstruction; do not weaken the allocator contract silently.
Done: a premise-free proof of the covers statement, its usable f1 libHeap adapter, focused affected build and standard-axiom audit, reproducible generator wired to drift checking, and accurate ledger.
Leave complete OCaml.Audit and integration to the lead. This does not close reset reachability, root registrations, named reserve, channel count migration or general formatting.
