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

Target: prove the native newlib integer-format decoder for the full successful formatInteger grammar, from the percent dispatch through flags/width/precision/one l modifier to the conversion-specific argument entry.
Prerequisite: reviewed full ParseFormatCall/FormatInt caller prefix. This packet decodes the resulting format; digit generation, padding output, allocation and the complete C_CALL2 return remain separate.
Files: OCaml/Vm/Primitives/Format (new decoder module), Bytecode/Data or a low format-facts module, existing VsaIris/Vsa/SnpSvfConv and its source templates only as needed, focused audits.
Inventory SnpSvfConv.ConvAt, svf_convStart, SvfSt, TabAt, IntAt and SvfLong before choosing an invariant. Existing ConvAt/IntAt fix flags=0/LONGINT, precision=-1 and width=0, so they cannot simply represent general flags/width/precision.
Introduce one named decoded-format observation and one reusable parser-loop invariant, parameterized by the actual format bytes and parsed fields. Use the existing snp_runF/generated step battery and shared loop kernel; avoid one copied proof per flag or digit count.
Derive a semantic decomposition of formatInteger success without evaluating huge List.replicate terms or changing its accepted domain. Include repeated flags, flag precedence, absent versus zero precision, decimal width, the native l modifier and d/i/u/x/X/o.
Prove width/precision arithmetic bounds from the successful result-length bound supplied by Fits (or state that result-length bound at this lower layer and provide its semantic implication). Do not infer int-sized width merely from the 32-byte format buffer; long decimal text can overflow native int arithmetic unless excluded by the result bound.
Relate those parsed fields to the actual native registers/stack sign slot at the real conversion entry, preserving SvfSt, original argument cursor, output and memory frames. A state with assumed post-parser registers/run is not a decoder proof.
Honor separate native signed and unsigned argument routes and exact source-byte order. Keep copied format/scratch/library separation explicit, and derive intermediate readbacks from native effects.
If the existing interface is too specialized, factor a generalized field invariant and retain the plain API as an instance. Edit generated files only via scripts/retarget_stdio_specs.py templates or the appropriate generator.
Done: checked full-grammar native decoder, semantic decomposition and field bounds, affected consumers, all-new-theorem audit and generator checks. List remaining conversion/output/allocation obligations precisely; do not claim the full formatter closed.
Keep GoodF1 unchanged, CustomMemCall named, and C4 round 2 waiting. Record dead ends and leave checked edits for lead review/integration.
