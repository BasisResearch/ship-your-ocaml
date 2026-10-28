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

Target: finish the preserved named-value invariant propagation so the complete OCaml build works without new premises hiding successful F1 calls.
Files: OCaml/Vm/Primitives/Named/NamedAt.lean; OCaml/Vm/{Repr,Caller}.lean; OCaml/Vm/Gc/NurseryTransport.lean; named payload and geometry producers; docs/lanes/a1-prims.md.
Start from existing WIP commits on this worktree; four recently repaired producers already build.
First repair NurseryGeometry.transport_ids/transport/frame_log/alloc at NurseryTransport.lean lines 76 and 173, mirroring StackGeometry transport.
Then rebuild affected consumers and migrate named-memory frame producers with shared abstractions.
Inspect /tmp/syo-prims-full.log for the last failure; do not redo the four repaired producers.
NamedNode currently imposes ASCII but primF1Impl accepts arbitrary bytes: generalize the byte/string bridge, never silently restrict GoodF1.
Done: named invariant producers build and audit, with honest named-key semantics; update lane log and report checked edits for lead integration.
If semantic mismatch is deeper, write the precise obstruction and preserve checked work for the lead.
