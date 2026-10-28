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

Target: repair custom-state heap ownership to use the caller's selected live-block ledger, with a checked obstruction to the old universal-ledger frame and real initial/frame/call producers.
Files: Vm/Gc/{CustomMem,F1Heap,ChannelCustomCount}.lean, Primitives/Channel/MlOpen.lean, counted opening/listing adapters, captured allocator consumers; generated files only via their generators.
CallerApart.free currently says forall H cap, HeapReady H cap c -> not (vsaFoot H a). HeapReady does not make H exhaustive: HeapAt.live/exact only constrain listed extents. The captured raw_heap has H=[] while real custom state includes heap-resident domain/table words.
First prove the precise obstruction at the captured cut using WhileMinAllocator.raw_heap/heap_transport and its image/capacity certificates: an empty-ledger HeapReady makes every arena byte vsaFoot []. Show the old apart field therefore cannot include an actual domain-resource/table byte. Do not claim CustomMemCall is globally inconsistent: empty Ready/Customs can make it vacuous.
Replace that universal ownership requirement with explicit custom-state ownership in the same selected ledger used by LibHeapAt and the caller allocation. Keep the other CallerApart separation fields; derive state-vs-fresh-record separation from actual owned bytes and FreshBlock, not a new arbitrary frame premise.
Produce initial ownership from the closed captured allocator ledger and actual custom-table/domain observations. Carry ownership through existing ordinary frames and named CustomMemCall return/growth, tying any returned heap/ownership to the same existential ledger.
Do not put custom_table into f1Covered without checking CallerApart.covered (those caller-write extents currently exclude custom state). If domain table-pointer observation is added, correct domainField and all real frame producers explicitly.
CustomMemCall stays the named native machine obligation. Do not hide a complete primitive return, arbitrary poststate coherence or the old impossible universal property in another named field.
Done: checked obstruction and repaired selected-ledger API with all affected opening/listing/count-frame consumers checked, focused allowed-axiom audit, generator/discipline checks, precise remaining full physical Customs/startup predicate obligations.
Preserve GoodF1, physical count semantics and actual C_CALL setup/return. Record the failed universal-ledger route in DEAD-ENDS; leave checked edits for lead integration.
