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

Target: close complete counted C_CALL3 and C_CALL5 rows by the actual F1 arity classification, with no native-return premise for impossible semantic branches.
Files: Bytecode/Semantics.lean (shared semantic lemma only), Sim/{CcallShort,CountedControlRows}.lean, counted row generators and focused audit modules.
Inspect every current primF1Impl pattern and primsF1. Source inspection finds F1 arities 1, 2 and 4; prove the classification rather than trusting that inspection or a list of names alone.
C_CALL3 passes accu::stack.take 2 and C_CALL5 passes accu::stack.take 4 only after the real stack-depth check. Include all outcomes (.ok, .exit, .raise, .callback, .unsupported) and reject malformed operands/negative/out-of-range primitive indices exactly as stepI does.
Reuse prim_arity/CcallShort where applicable, shared run laws and ArmOutcome interfaces. A successful return contract alone does not exclude exit/halt; account for caml_sys_exit's unary pattern explicitly.
Derive complete OpArm P (CountedLoopAt Customs f1Layout P) for both opcodes from semantic impossibility at InF1/GoodF1 sites. Do not constrain the primitive table, add a new guard or assume unreachable C_CALL3/5.
Tie any updated opcode census to these actual whole-row terms. Preserve all 129 prior row terms, named CustomMemCall and counted BarrierGrowthFull boundaries; full C_CALL1/2/4 remain open.
Factor the shared wrong-arity/operand argument before instantiating the two rows; keep generated facts in their generator and audit all new theorems.
Done: two checked whole counted rows, exact 131/134 supplied census relative to existing named suppliers, focused affected build/axiom audits and generator checks, precise remaining C_CALL1/2/4 obligations.
If any primitive really admits three/five arguments, return the exact checked obstruction to this proposed classification and retain that opcode as open. GoodF1 stays unchanged.
Update lane log/PHASES/DEAD-ENDS and leave checked edits for lead integration.
