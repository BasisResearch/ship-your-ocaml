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

Target: prove a named-node/key resource bound for reachable GoodF1 states from Fits, replacing the absent fixed name/count guards for that component.
Files: OCaml/Bytecode/{NamedValues,Data,Semantics}.lean; OCaml/Fragment.lean; OCaml/Vm/Gc/{F1Heap,NamedLedger}.lean or a shared named-resource module; relevant audit/ledger.
Start by inspecting current namedLedger/NamedRoom consumers. maxNamed=16 and maxNameLen=64 are not GoodF1 guards; do not add guards or assume those bounds.
A candidate route is key provenance: each registered first-NUL byte key comes from an immutable heap byte object; distinct keys require distinct source objects. Verify every F1 heap writer before relying on this.
SETBYTESCHAR is F2, so the proposed reusable mutable-buffer counterexample is outside this task's domain. This fact alone does not prove provenance or the resource bound.
Track actual C-string bytes through namedValueKey, using the landed full-byte bridge. UTF-8 byte size of the Lean String is not the source-byte length. strOf? also accepts fully initialized partialBytes via mapM id: cover it or derive its absence from the actual initial/preservation facts.
Prove preservation using the shared run kernel/invariant interface, not hand induction on Reach. Include the actual initial named table and replacement-versus-fresh registration cases. Reuse Run.iter_inv and the Reach/StepsN-to-bcK bridge; reuse Heap.get_alloc_old/get_alloc_fresh (currently Logic/Symbolic.lean) and Sim/HeapAllocAll for allocation sequences, factoring a lower shared module if imports would cycle.
Bound node/key allocation charge using actual vsaChg/rounding and the heap-word budget; derive enough initial arena capacity rather than guessing a new constant. Candidate arithmetic to prove: roundUp16 (prefixLength + 24) <= 16 * (sourceLength / 8 + 2) when prefixLength <= sourceLength, so injective source assignment bounds total node credit by 16 * heap.words (4,192,704 at g1Budget).
Existing-name root-class changes can remove and reinsert skiplist cells (globroots.c:135-162). Distinct keys do not bound those allocation calls; keep cell reuse/refund accounting explicitly open instead of multiplying one cell per key.
The existing vsaRoomB counts only heapEnd - top, not free-bin bytes; FreeRunAll.fOK_chg gives top <= top0. An interior free does not imply k + charge in this interface. Keep bin-aware reuse separate.
Connect the node/key bound to an explicit selected-ledger reserve component; retain physical allocator/root operations and repeated root-cell charges as separate obligations until supplied.
Done: a checked reachable-state node/key bound and reserve component replacing absent guards, focused build/standard-axiom audits, accurate remaining consumers. If a route is false, record the precise obstruction without weakening GoodF1.
Leave checked edits for lead review and integration. Do not claim the general registration C_CALL2 supplier closed from a resource lemma alone.
