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

Target: reconstruct the actual F1 runtime after native channel opening, reusing the checked selected-heap/spatial return and the listing runtime component proofs where applicable.
Files: Sim/{PrimOpenOutReturns,OpenOutReturn,OpenOutFrame,OpenOutObserved,OpenOutPlaced}, Primitives/Channel/MlOpen, Gc/{F1Heap,F1Runtime,CustomMemCredit} and focused audit/generators.
Read the latest listing handoff first; coordinate the selected custom-credit/spending interface rather than inventing a second contract.
OpenOutRuntimeAt.after currently receives LibHeapAt and OpenedOut but not the original OutInput/OutNursery. The existing spatial_heap, covered_kept and domainField_kept helpers need those actual inputs. If they cannot be recovered from the retained native evidence, thread them from open_out_return's existing inputs through the interface; do not assume an arbitrary stack/nursery frame.
Use OpenedOut.spatial_heap's one returned ledger, actual fresh record, named/custom ledgers and allocIn. Prove open-list membership, alignment, record/payload separation, dynamic remembered/custom separation and unchanged table geometry from the actual malloc/custom return.
Reconstruct RuntimeOk/F1Pins using native static/domain/covered frames and the actual young_ptr minus 24. Preserve code, stack, primitive-table, atom and console pins through actual address/window bounds.
Capacity is a separate native duty: the record allocation spends 65616, while reserved uses recordCharge 2^17 per future channel. Track the actual residual custom-table charge on the same H/cap; arbitrary existential HeapReady with capacity zero is not a spending law.
CustomMemCall remains named. Any refinement must be a concrete native input-credit and returned-spending/table-shape duty with actual caller producers, never a whole-opening runtime or returned LibHeapAt assumption.
Done: checked opening after-runtime component(s), coherent actual-input API, affected counted opening/listing/C_CALL builds and all-new-theorem focused audit. Claim the complete supplier only if capacity and every invariant field are actually supplied; otherwise list the precise native-credit residual for the next bounded task.
Do not strengthen GoodF1, infer maxNamed/name-length bounds, assume a primitive result or erase physical counts. Keep BarrierGrowthFull with G2 and C4 round 2 waiting.
Record refuted routes; leave checked edits for lead review/integration.
