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

Target: check and repair the custom contract's global record-separation/frame incompatibility, using the selected-ledger ownership work already present.
Files: Vm/Gc/{CustomMem,CustomLedger,F1Heap,ChannelCustomCount}.lean and actual record-writing/opening/listing/frame consumers; respect generated Layout.
Candidate obstruction: CustomMemCall.frame accepts any c' preserving state bytes and Caml_state, and returns state c' a iff state c a. CallerApart.records then requires separation from every OpenChannelList in c'. That list predicate only reads the head and next words; it carries no allocator ownership.
Check the precise conditional contradiction at a valid pinned domain D: Ready k c, word c Caml_state = D, and state c (D+off_extra_heap_resources_minor). Form c' by setting the opened-list head to a=D+96 and the next word at a+48 to zero. Derive write separation from CallerApart.static/domainField, preserve Caml_state, apply frame, build OpenChannelList [a], and contradict the returned global records field. Use generated offsets, actual writeLog read/frame lemmas and no Sail execution claim.
Do not claim global inconsistency: empty Ready/state may satisfy the abstract contract. This is a contract obstruction to the intended nonempty physical producer, if the candidate checks.
Repair spatial separation as a local selected-ledger invariant for actual represented channels and named roots, rather than an unconditional law over arbitrary memory linked lists. Keep genuinely footprint-local custom accounting/quietness/frame and native call obligations named.
Derive record-write separation from actual owned extents plus the selected spatial invariant; strengthen real startup/frame/allocation producers as needed. Dynamic custom storage must remain apart from real records/other live regions, including after native growth, in the same returned heap ledger.
Review CallerApart.named for the analogous dependency on arbitrary external named-table writes; do not leave the same global-frame problem under a different field. Separate checked evidence from any still-unchecked candidate.
No new arbitrary preservation, whole primitive return or poststate coherence premise. Every added spatial field needs a real initial/frame/call producer or an explicitly recorded native machine obligation at its actual call boundary.
Done: checked precise obstruction (or checked refutation of the candidate), coherent local API and affected opening/listing/counted frame builds, focused allowed-axiom audit and exact remaining physical CustomMemCall supplier obligations.
Update DEAD-ENDS, PHASES and the lane log; preserve GoodF1 and leave checked edits for lead integration.
