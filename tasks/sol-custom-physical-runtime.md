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

Target: supply the concrete physical custom startup/accounting and call-runtime observations needed to instantiate the counted invariant, while retaining the native CustomMemCall as the accepted named obligation.
Prerequisite: selected CustomSpace repair is present. Files: Gc/{CustomMem,CustomLedger,ChannelCustomCount,F1Runtime}, counted entry, opening/listing native-call producers and runtime-read/Layout generators.
First audit the actual custom.c/memory.c/native call's read set. CustomMemInput currently supplies leaf/heap/register/frame/nursery facts but no explicit ratio, heap-size or memprof pins; CustomMemCall.frame preserves only state bytes and Caml_state. Do not infer arbitrary outside runtime reads from that frame law.
Separate read-only call-runtime pins from the mutable custom-state footprint when appropriate. Add only concrete native preconditions and derive them at actual opening/listing call sites from strengthened real runtime producers, never a whole-primitive/poststate premise.
Use generated captured read certificates to establish actual initial resource words, custom-table/domain identity, occupancy, bounds and required parameters. Preserve each observation through actual caller write windows and native returned effects; captured memory is not reset execution.
Define the complete physical Customs/Ready relationship with actual resource observations, not just table occupancy or the abstract channel-refcount sum. Retain unique counts and all real accounting frames, with pointer identity either observed in the framed footprint or supplied by a separately proved stable pin.
The rational quietBound_spec alone does not prove native binary64 rounding/threshold behavior. Reuse actual arithmetic semantics or kernel-checked finite bit-pattern facts where needed; identify any remaining exact numeric native obligation without claiming it closed.
CustomMemCall still owns the actual allocation/table-growth/quiet native return and its exact count transition. Do not add new unrelated trusted primitive summaries, silently widen state without its frame producers, or make an arbitrary external observation a global consequence of Ready.
Done: concrete full physical startup zero and read-only call-context producers, preserved through counted entry and actual opening/listing setup, with exact residual native obligations, affected builds and all-new-theorem audits. GoodF1 and standing G2 boundary remain unchanged.
Update PHASES, lane log and DEAD-ENDS; leave checked edits for lead review.
Coordination: sol-outlist-runtime-local.md handles the unconstrained stack/allocator-frame supplier and custom-table credit gap. Current CustomMemReturned.heap alone does not bound returned capacity; do not report LibHeapAt.room preserved without actual charge/reserve evidence.
