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

Target: integrate the bounded original-entry least-large split into the real caml_alloc_shr_for_minor_gc wrapper, preserving its representation and returning initialized size/tag/color plus original ABI from original caller facts.
Read the latest a6 log and DEAD-ENDS entries. Reuse BestFitEntryLargeReturn/EntryLargeInput, AllocLargeWrapper, AllocWrapperCore, AllocFinish, AllocSuccess, AllocSelect/AllocColor and LogWindows/LiveFrame; do not duplicate their execution proofs.
Files: Gc/{BestFitEntryLargeReturn,AllocLargeWrapper,AllocWrapperCore,AllocLarge,AllocFinish,AllocSuccess,AllocSelect,AllocColor,BestFitPreservation} plus a small dedicated original-entry wrapper module and audit.
Scope: positive requests <=16, no suitable small class, bounded bitmap, and request+17<least source size. Preserve the old high-bit interface counterexample. Arbitrary trees, requests>16, heap expansion and collection stay explicit remaining work.
Build a named original-caller interface with actual wrapper inputs, bounded small representation, selected full source geometry, native-frame separation, original phase/sweep/accounting reads and explicit no-major-slice arithmetic/credit conditions.
EntryLargeSource alone is only geometry/nonwrapping extent, not full allocator ownership or upper arena membership. If ownership is needed, consume the selected ledger/major-arena invariant explicitly; do not describe the existing lower bound as full ownership.
Derive the wrapper-prepared representation and every missing-slot/filter/large/saved-bank/continuation observation from actual prologue effects and those original facts. No assumed searched/allocated configuration, run, whole AllocLarge.Conditions or opaque returned invariant as an entry premise.
Reuse actual AllocWrapperCore.enter/complete and existing free-list and finish summaries. Keep source/list disjointness through header initialization and accounting; return bounded small representation, shortened source, allocated separation, exact header/color and the composed actual write log.
Use existing AllocColor semantics to state the actual phase-selected color. HeaderOk alone drops color bits, so do not call it a color theorem. Natural allocated/free counters require explicit nonoverflow/nonunderflow credit; derive their original-read forms without claiming credit from representation alone.
Done: checked original-wrapper summary with concrete internal-condition suppliers and representation-preserving post, affected wrapper/major-allocator consumers and all-new-theorem audit. If a genuine invariant seam stops composition, isolate the exact smallest original-state premise and record it, not a whole-body assumption.
Keep GoodF1 unchanged; no full G2/BarrierGrowthFull claim from this branch. Update PHASES/a6 log/DEAD-ENDS and leave checked edits for lead review.
