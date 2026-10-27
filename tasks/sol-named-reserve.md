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

Target: replace the unjustified fixed named-key limits with a resource bound proved for reachable GoodF1 states from Fits.
Files: OCaml/Bytecode/{NamedValues,Data,Semantics}.lean; OCaml/Fragment.lean; OCaml/Vm/Gc/{F1Heap,NamedLedger}.lean or a shared named-resource module; relevant audit/ledger.
Start by inspecting current namedLedger/NamedRoom consumers. maxNamed=16 and maxNameLen=64 are not GoodF1 guards; do not add guards or assume those bounds.
A candidate route is key provenance: each registered first-NUL byte key comes from an immutable heap byte object; distinct keys require distinct source objects. Verify every F1 heap writer before relying on this.
SETBYTESCHAR is F2, so the proposed reusable mutable-buffer counterexample is outside this task's domain. This fact alone does not prove provenance or the resource bound.
Track actual C-string bytes through namedValueKey, using the landed full-byte bridge. UTF-8 byte size of the Lean String is not the source-byte length.
Prove preservation using the shared run kernel/invariant interface, not hand induction on Reach. Include the actual initial named table and replacement-versus-fresh registration cases.
Bound the combined node/key and worst-case skiplist-cell allocation charge using the actual vsaChg/rounding and heap-word budget; derive enough initial arena capacity rather than guessing a new constant.
Connect the bound to an explicit selected-ledger reserve suitable for registration; retain physical allocator/root operations as separate named obligations until supplied.
Done: a checked reachable-state resource bound and usable reserve contract replacing absent guards, focused build/standard-axiom audits, accurate remaining consumers. If a route is false, record the precise obstruction without weakening GoodF1.
Leave checked edits for lead review and integration. Do not claim the general registration C_CALL2 supplier closed from a resource lemma alone.
