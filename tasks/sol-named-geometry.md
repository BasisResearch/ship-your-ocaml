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

Target: supply physical named-node separation in the represented geometry, then finish the named payload consumer migration.
Files: OCaml/Vm/{Repr,Caller}.lean; OCaml/Vm/Sim/{Invariant,ArmGeometry,LoopGeometry,PayloadWindows,NamedGeometryObstruction}.lean; OCaml/Vm/Gc/Nursery*.lean and geometry/Loaded producers.
Start from the preserved named worker checkpoint; read its current lane log and focused audit results.
The checked named_domain_alias witnesses missing domain separation in the OLD geometry, not unreachable execution or a user-only decision.
Add named ownership/bounds/separation fields alongside existing object/channel facts; prove their transport and empty-name startup case.
Derive PayloadCoreOutside.named from LogWindows, including field stores, and finish native-stack/object/channel frame consumers using shared named frame lemmas.
Use actual malloc ownership for allocating paths; never infer nodes lie in fixed f1Covered extents and do not assume absent maxNamed/maxNameLen BcSem guards.
Keep the obstruction only as an explicit old-geometry witness, or document its removal when the stronger invariant rules it out.
Done: affected representation/geometry/payload consumers and the complete OCaml target build; focused new-theorem audits pass; no new GoodF1 restrictions or hidden successful-call premises.
Leave checked edits for lead review. Record any remaining named primitive or allocation producer obligation precisely.
