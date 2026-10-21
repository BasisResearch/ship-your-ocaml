Binding rules: read CLAUDE.md, PHASES.md, PLAN.md and your lane log; user directions override older briefs.
Run scripts/abs_inventory.sh before proof work; reuse mandatory abstractions by name.
No sorry, axiom, native_decide, bv_decide, heartbeat increases, or edits to generated outputs.
Edit generators; audit new theorems with only propext, Classical.choice, Quot.sound.
Before each build check free -g (available >=25 GB); one build per worktree.
Run all Lean through systemd-run --user --scope -q -p MemoryMax=12G env LEAN_NUM_THREADS=2.
Do not add ulimit -v: virtual reservation breaks the large import closure; the cgroup enforces 12 GB.
Work only in this worktree; preserve inherited WIP and never force-push or reset it away.
BarrierGrowthFull stays with G2; CustomMemCall remains a named premise; C4 round 2 waits for F1.
Read docs/lanes/DEAD-ENDS.md before choosing a route; record newly refuted routes there.
Build affected modules; register audits and update lane log/PHASES accurately; commit small checked steps.
Land only via scripts/integrate.sh (full gate and serialized fast-forward push); never bypass a failed gate.
No subagents or other Codex workers. Finish with exactly RESULT: landed <commit> or RESULT: stuck <where>.

Target: finish the preserved named-value invariant propagation so the complete OCaml build works without new premises hiding successful F1 calls.
Files: OCaml/Vm/{NamedAt,Repr,Caller}.lean; OCaml/Vm/Gc/NurseryTransport.lean; named payload and geometry producers; docs/lanes/a1-prims.md.
Start from existing WIP commits on this worktree; four recently repaired producers already build.
First repair NurseryGeometry.transport_ids/transport/frame_log/alloc at NurseryTransport.lean lines 76 and 173, mirroring StackGeometry transport.
Then rebuild affected consumers and migrate named-memory frame producers with shared abstractions.
Inspect /tmp/syo-prims-full.log for the last failure; do not redo the four repaired producers.
NamedNode currently imposes ASCII but primF1Impl accepts arbitrary bytes: generalize the byte/string bridge, never silently restrict GoodF1.
Done: named invariant producers build and audit, with honest named-key semantics; update lane log and land through scripts/integrate.sh.
If semantic mismatch is deeper, write the precise obstruction and preserve checked work for the lead.
