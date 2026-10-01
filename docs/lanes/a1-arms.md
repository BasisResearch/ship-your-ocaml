# Lane a1-arms

## OFFSETINT width correction needed in a2-sem

The pinned OFFSETINT body uses `slliw` at `0x8000324c`: the operand is
shifted in 32 bits and then sign-extended to 64. `stepI` currently shifts
`BitVec.ofInt 64 n` in 64 bits. For operand `0x40000000` and accumulator 64,
these produce different represented integers. `offsetint_width_obstruction`
(`OCaml/Vm/Sim/OffsetWidth.lean`) kernel-checks that difference using the
exact Sail operand expression from the generated `tr_offsetint` postcondition.
The five-step machine body and ELF-image projection are proved. This is a
word-level obstruction, not a complete `Loaded`/Sail whole-program result.

Reproduce: `python3 scripts/probe_offset_width.py --expect-model 1`.
It compiles a Stdlib-free OCaml 4.14.4 program testing `size () + 1 > 0`,
then changes only OFFSETINT's operand to `2^30`. Baseline host/runbc exit 1;
patched host exits 2 while runbc exits 1. The script reads opcode numbers
from `gen_opcodes.opcodes`, and supports `--expect-model 2` to validate the
repair. No assumption excluding the operand was added to the headline.

A2-sem must match the pinned 32-bit shift for OFFSETINT. OFFSETREF has the
same 64-bit expression in `stepI` and `slliw` at `0x80003230`, so needs the
same width correction; its complete store arm is not proved here. The
arithmetic obstruction is independent of `stepI`, allowing it to remain as
regression documentation after the fix. Other arm families remain unblocked.

Default-limit 24 GiB checks: OFFSETINT body/pins 5.56s (segment 2.1s),
arithmetic witness 3.60s (module 2.3s), peak process RSS below 2 GiB.
CONSTINT landed as `9786220` with the full gate passing.

## Signed relative branch

`branch_arm` (`OCaml/Vm/Sim/Branch.lean`) composes the generated four-step
BRANCH body with dispatch, preserving the accumulator, memory and remaining
VM/platform state. `target_int` and `relative_code_word` prove the signed
relative bytecode-to-machine address identity, for forward and backward
branches and arbitrary operand-base offsets. `OperandAt.read32` factors the
read-only prefix observation shared with CONSTINT.

The represented bridge takes successful semantic `target` computation and
the existing ordinary operand/dispatch/runtime-frame premises. Its targeted
build is 1.0s (1.57s wall); the final shared-helper rebuild takes 3.91s, with
peak process RSS below 2 GiB under 24 GiB. CONSTINT rebuilds after adopting
the same operand helper. Fixed environment/field arms landed as `b52357e`
with the full gate passing; BRANCH brings the conditional arm count to 25.

## Fixed environment and field loads

`gen_field_arms.py` emits `envacc1_arm`–`envacc4_arm` and
`getfield0_arm`–`getfield3_arm` over their census-generated total-load bodies.
`field_selection` (`FieldRead.lean`) derives the source pointer and placement
witness from successful abstract lookup plus `HeapRepr`. `FieldSelection.read`
uses a1-prims' `VmPayload.object_at` to recover the selected word and proves
it is an existing live root. Every bridge then uses `accu_arm` to restore the
full data/platform/loop state.

`RamReadAt` (`ReadGeometry.lean`) is the shared natural-address RAM/HTIF
contract and projects to the existing `ReadWindow` interface. `CodeReadAt`
is its four-byte specialization; load addresses and HTIF symbols use `Layout`
or abstract placements. Field geometry is still an explicit premise.
`represented_register` is shared in `ArmInput.lean`; field and unary bridges
reuse its value-uniqueness proof. No `Running` or headline fields are weakened.

All eight families pass separately under 24 GiB at default limits:
ENVACC1–4 6.24/6.56/5.60/5.49s, GETFIELD0–3 6.52/6.16/6.48/5.75s.
Each bridge elaborates in 1.2–1.5s; peak process RSS stays below 2 GiB.
This brings the conditional represented arm count to 24. Unconditional
`ArmSim` entry/next/halt and the machine `whileMin` result remain open.
The OFFSETINT obstruction landed as `3a514fc`; main now includes A0-boot's
`bc63ae6` captured-entry `Loaded` certificate, including primitive bindings.

## Primitive binding repair

The obstruction landed as `2bb35a3`. `primitive_binding_obstruction` now
retains that checked result against the explicit legacy `UnboundLoaded` /
`UnboundRefinement` snapshot. The generated probes have identical code,
heap, globals and world; swapping only word-size/int-size names in PRIM
changes the exit from 64 to 63. Host ocamlrun, runbc, and Lean agree; both
programs are `Good` and fit any budget covering their initial heap. The
obstruction is conditional on a loaded witness, not a concrete boot proof.

Production `LoadedAt` and `VmReprAt` now carry named `PrimitiveBindings`.
It ties every `P.prims` entry to the function pointer read by C_CALL.
`PrimitiveEntries.lookup` is generated from all 403 parallel name/address
entries in the pinned ELF, checked against symbols and `.text`; its balanced
lookup has named facts for all 30 F1 primitives. The table symbol and contents
offset come from `Layout`, with the offset recovered from C_CALL1's load.
`loaded_probes_disjoint` proves the old ambiguity is excluded.

`PrimitiveBindings.frame` preserves the metadata under memory equality;
CONST0/NEGINT’s shared restoration uses it. `primitiveBindingsEqv` uses
`Eqv.all` / `guard` / `observe`; `VmImage.primitives` asks the collector to
preserve the selected function-pointer observations. No abstract heap pointer
is renamed. The existing `vmReprAt_reloc` and GC `LoopHead` consumer build.
A0-boot must supply `LoadedAt.primitives` at the cut. The newly landed
`WhileMinEntry.EntryControl` carries that explicit obligation; its `loaded`
assembly consumes it, and `fillZero` preserves it via `of_words` and the
existing `bytesT_memEqv` law. C_CALL arms can consume
read-only primitive memory frames; mutating summaries will need the metadata
frame as well. Primitive bodies remain a1-prims-owned.

`OcamlrunRefinement` was compared byte-for-byte with the pre-repair definition
and is unchanged. The HTIF obstructions remain checked, with their memory
frame extended to preserve primitive bindings.

Validation: resolver 14s, representation 1.2s, refinement 1.1s, relocation
2.1s, legacy/disambiguation regression 2.8s, GC invariant 1.0s. CONST0 and
NEGINT rebuild at 1.1s / 1.2s; targeted runs remain below 2.08 GiB under
24 GiB. No proof budget changed. Drift, discipline and abstraction checks
pass; the full integration gate passed and landed the repair as `9eeb667`.

## CONSTINT and ordinary operand reads

`constint_arm` (`OCaml/Vm/Sim/Constint.lean`) composes the generated
five-instruction load/tag/advance body with dispatch and full representation
restoration. It returns `.int (BitVec.ofInt 63 w.toInt)` and advances PC by
two, exactly matching the signed bytecode operand. `tag_word32` uses the
existing sign-extension and shift/add laws; no operand values are enumerated.

`OperandAt` names the fetched code word, non-cache position and code RAM
geometry. `code_read`, `CodeReadAt.toNat` and `OperandAt.read` give the common
observation bridge; `ArmInput.of_repr` reuses the same facts. `codePc_add`
generalizes the existing successor address identity. These remain explicit
input facts, not a claim of unconditional `ArmSim.next`.

Default-limit 24 GiB builds pass: body/pins/arithmetic 5.70s; represented
bridge plus shared helpers 5.61s (bridge 1.6s), peak process RSS below 2 GiB.
BOOLNOT landed as `5d473b0` with the full gate passing. CONSTINT brings the
represented conditional arm count to 16.

## Unary tagged subtraction

`gen_unary_arms.py` emits both NEGINT and BOOLNOT represented bridges from
one template over the census-generated four-instruction bodies. `tag_sub`
proves the 63-bit modular subtraction identity once; `tag_neg` and `tag_not`
instantiate it for machine constants 2 and 4. `boolnot_arm` restores the
exact `stepI` result `1 - n` for every integer accumulator, without assuming
it is a Boolean. It retains the existing explicit `ArmInput` / runtime-frame
premises. All new body, image and bridge theorems are audited and generated
artifacts are drift-checked.

BOOLNOT builds in 8.14s (bridge 1.7s), under 2 GiB peak process RSS and the
24 GiB cap. ACC0–ACC7 landed as `32025f5` with the full gate passing; BOOLNOT
brings the represented conditional arm count to 15.

## ACC0–ACC7 representation bridges

`accu_restore` and `accu_arm` (`OCaml/Vm/Sim/Immediate.lean`) generalize the
shared restoration/composition to represented accumulator words. They consume
`VmPayload.accu_of_root` from a1-prims; immediate arms specialize this rule
without a second heap/root proof. `stack_value_root` in `StackAcc.lean` selects an
existing stack root, and `stack_slot_nat` derives non-wrapping addresses from
stack shape and the represented `stack_high` word.

`gen_acc_arms.py` emits `acc0_arm` through `acc7_arm`; the census/site/segment
pipeline emits every machine body and ELF pin. Each bridge selects the exact
abstract stack value, advances PC by one, and restores all data/platform/loop
fields. The only extra load premise is the shared `ReadWindow` RAM/HTIF
geometry; absent bytes remain total zero reads. Dispatch readiness and runtime
memory stability remain explicit, so these are conditional represented arms.

Separate default-limit builds under 24 GiB pass: ACC0 3.96s including shared
restoration, ACC1–ACC7 4.51/4.53/6.66/5.16/5.55/5.60/5.70s. Each generated
bridge elaborates in 1.0–1.4s; peak process RSS remains below 2 GiB. The
14 represented arm bridges are CONST0–3, NEGINT, ISINT and ACC0–7; generic
ACC has its machine body only. The F1 `ArmSim` exit remains open.

## ISINT representation bridge

`isint_arm` (`OCaml/Vm/Sim/Isint.lean`) composes generated dispatch/ISINT
segments through `immediate_arm`. `IsintArithmetic.lean` proves the body's
shift/mask/add result equals `Val.ofBool s.accu.isInt` under `EvenPlace` and
the semantics' non-raw-value condition. `EvenPlace` requires even code and
heap placements; it is an explicit premise, not yet part of `Running`.
`isint_not_valWord` is a checked value-level counterexample: a pointer placed
at address 1 has the same word as integer zero, so `valWord` alone cannot
justify the classification. This is not a full `Running` counterexample.

Landed as `48219ed` with the full gate passing. Both files build at default limits under 24 GiB: arithmetic 1.2s, bridge
1.5s, total wall 3.46s, peak process RSS below 2 GiB. The new theorem names
are included in the axiom audit. The constant-arm family landed with the
full gate as `ebf75db`.

## Constant-arm family

`immediate_arm` (`OCaml/Vm/Sim/Immediate.lean`) composes the shared dispatch
run, any generated immediate-result body, and `immediate_restore` once.
`DispatchPost.image` supplies the body image from dispatch's memory frame.
CONST0 and NEGINT now consume this rule. `gen_const_arms.py` emits represented
CONST0–CONST3 bridges; `gen_arm_pilot.py` emits their machine bodies, sites,
ELF pins and image projections from the census. The new `const1_arm`,
`const2_arm`, and `const3_arm` restore the exact semantic PC/accumulator result
and every data/platform/loop component, including primitive bindings.

These remain conditional on `ArmInput` and `MemoryStable L.runtimeOk`;
no unconditional `ArmSim.next` case is claimed. Axiom and generator-drift
checks cover the new family. Separate default-limit builds under 24 GiB:
CONST0 plus composition 3.52s; CONST1 5.92s, CONST2 4.74s, CONST3 4.58s.
New constant bridge elaboration is 1.0–1.4s; peak process RSS below 2 GiB.

## Current status

The repair (`ef4e701`), CONST0 (`3229c53`), and ISINT/shared ALU adapter
(`7994562`, integration head `dac2c19`) have landed through
`scripts/integrate.sh`. The delayed integration completed successfully
when host memory recovered; all gates, including the 16 ALU smoke sites,
passed. NEGINT subsequently landed as `e2777bc` with all gates passing.
ACC/ACC0 subsequently landed as `dd48ca0` with all gates passing.
Counted contracts landed as `a22f2b9`; register/console frames as `ee18571`.
Dispatch and checked pin lookup landed as `2857cd0` / `7e2ae1a`, after
a full gate and a rebase over the primitive lane’s signed comparison.
The table facts landed as `c7989c8`, with the full gate passing.
Composed dispatch landed as `fe72ca4` with the full gate passing.
The CONST0 representation bridge landed as `85275ba` with all gates passing.
NEGINT and post-migration checks landed as `c26cecd` / `50aa08d`, with the
full gate passing against the new image.
The F1 exit remains open.

F1 primitive machine summaries belong to **a1-prims**, including all
`primsF1` C_CALL targets. This lane will consume their represented
call-site/return-state contracts through named premises until they land;
it will prove the generated arm prefix/suffix and composition, not the
primitive bodies. No C_CALL arm has yet been discharged.

After F1, continue with F2, F3, F4, and F5 arms in order as a2-sem lands
the semantics; primitive summaries continue to come from a1-prims.
Re-read the brief's “After F1” section at that transition, including F3
method caches, F4 callback simulation, and F5 OS interfaces.

## ELF migration

Rebased onto A0-boot’s `272e436` / `7fa1750` fixed-`.embed` migration.
Pinned ELF SHA-256: `b055163e2280efbec1d16c255afccf31e23315f9f37a7ffcba5bbed0850b1c99`.
Regenerated `gen_ocaml_image.py`, `gen_arm_pilot.py`, `gen_alu_pilot.py`,
and `gen_dispatch_table.py` after the rebase; all outputs agree with the
migrated artifacts. Function addresses remain fixed. Data references use
`Layout`; load-contract RAM bounds remain architectural limits.
The old integration attempt was stopped after its automatic migration rebase
so regeneration preceded further validation. Post-migration checks precede landing the current NEGINT bridge.
All six generated families rebuild successfully at default limits. CONST0’s
full dependency rebuild took 88.61s, peak process RSS 2.52 GiB; NEGINT,
ISINT, ACC0, and ACC then took 2.38–3.48s each, below 2.07 GiB.
The dispatch segment and named boundary each rebuilt in about one second.

## Current contract

Foreman's approved repair is implemented. `OcamlrunRefinement` retains its
exact definition; `ArmSim` now establishes/preserves/consumes `Running`.
The representation has separate named data, platform, and fixed loop-register
parts (`OCaml/Refinement.lean:100`). No additional simulation premise was
added to the headline theorem.

* `PlatformOk` (`OCaml/Vm/Platform.lean:28`) carries the existing Sail
  `GoodState` (including `htif_done = false`), `ExecutableImage`, and
  `L.runtimeOk`.
* `ExecutableImage` pins the approved OCaml ELF's complete `.text` and
  `.rodata`, including the jump table. The old WHILE `FixedImage` literals
  are NOT used as the image. Only its generic `FixedBytesLoaded` predicate
  is reused. `scripts/gen_ocaml_image.py` emits balanced 256-byte page
  lookups from the SHA-pinned ELF; check_all a5 enforces generator equality.
  A0-lib's code-pin projections can use this common range interface.
* `LoopRegisters` pins the dispatch table, opcode bound, pending-signal
  symbol and domain-state symbol registers. `gen_layout.py` extracts and
  checks their initialization pairs in the interpreter prologue. Variable
  pc/sp/accu/env/extra registers remain in `VmReprAt`.
* A0 boot must now establish `LoadedAt.platform`. `Loaded.platform` exposes
  that obligation; `Loaded.runtime` retains its original interface. The
  prologue must additionally establish the fixed loop registers.
* Platform and loop-register fields have no abstract heap placement.
  `OCaml/Vm/PlatformReloc.lean` supplies `platformEqv` and `loopRegistersEqv`
  and the proved `platformOk_reloc`/`loopRegisters_reloc` transports (lines
  31 and 56). Collector control/runtime restoration and immutable-byte
  frames remain explicit typed obligations, not assumed preservation.

## Proved

* `Vsa.Sim.PinsHold.get` (`Vsa/Sim/PinLookup.lean:10`) is the shared
  finite-index accessor for register-pin lists. The segment generator uses
  it for pin reads and bundle restriction, eliminating deep positional
  conjunction projections. Its index bound simplifies only list lengths.
  Dispatch's first full gate exposed the old generator's positional
  projections; this fixes the generator without a discipline exemption.

* `Vsa.Sim.tr_dispatch` (`OCaml/Vm/Sim/DispatchSegment.lean:22`) proves
  the in-range eight-step loop-head path: opcode load, bound branch,
  jump-table offset load, and indirect jump. It exports `TripleN 8`, memory
  equality and `StepFrameOut`. `dispatch_loaded` supplies instruction pins.
  The path starts at the census loop head and follows the decoded taken
  branch; no data symbol is hard-coded. RAM/HTIF bounds, opcode guard, and
  target alignment remain explicit. A bridge from Running and the pinned
  jump table to these conditions and the selected arm address is still open.
* The shared segment front end now names branch site variants consistently
  with `gen_sites.py`; indirect-jump output can retain the exact machine
  target expression without an unnecessary rewrite premise.

* The shared generator now exports a `StepFrameOut` component for every
  pilot body, through its optional `frame_origin` parameter. The caller
  supplies the incoming state; the post preserves console output and all
  registers outside the computed write log. One `chain_frame_out` fold
  consumes the generated observations. Memory equality and `TripleN`
  counts remain in the same contract. This uses the existing frame
  abstraction rather than per-site, per-register proof threading.

* The five generated body theorems now return the existing `TripleN`
  instead of forgetting their step counts: CONST0/NEGINT/ISINT/ACC0/ACC
  have lower bounds 3/4/5/3/6. `TripleN.toTriple` retains ordinary triple
  use. The shared generator's optional `counted` mode uses
  `Steps.toN_of_stepsEq` from `Vsa.Sim.StepCount` (the run-kernel counter
  law), not a second induction on machine runs. Calls/custom postconditions
  remain outside this mode; the existing SegSt restriction checks that.

* `Vsa.Sim.tr_acc0` and `Vsa.Sim.tr_acc` in
  `OCaml/Vm/Sim/Acc0Segment.lean:20` and `AccSegment.lean:20` prove the
  three- and six-instruction stack-access bodies. `acc0_loaded` and
  `acc_loaded` project the code pins from the full image.
  The shared segment adapter now handles `ld_tot`, `lw_tot`, and `lbu_tot`;
  the pilot selects total loads automatically. ACC checks a loaded index
  flowing through ALU instructions into a later load address. The generated
  proof uses existing `RamReadLoad` lemmas, without byte-presence or alignment
  premises. RAM bounds and HTIF disjointness remain explicit obligations;
  the representation bridge must establish them.

* `Vsa.Sim.tr_negint` (`OCaml/Vm/Sim/NegintSegment.lean:20`) proves the
  four-instruction NEGINT body, including the subtraction of the incoming
  tagged accumulator from 2. `negint_loaded` projects its image pins.
  Generated through the same family pipeline without new proof machinery;
  abstract semantics and full representation/frame composition remain open.

* CONST0 pilot landed as `3229c53` through `scripts/integrate.sh`.
* Second generated arm body: `Vsa.Sim.tr_isint` in
  `OCaml/Vm/Sim/IsintSegment.lean:20`, five instructions including SLLI and
  ANDI. `isint_loaded` derives its local code pins from `ExecutableImage`.
  Raw machine values are threaded through repeated writes by the generator.
  The abstract-value bridge still needs placement/alignment facts and the
  runtime frame and data bridge; no `ArmSim.next` case is claimed.
* Shared `scripts/syi/alu_classes.py` connects classification, def-use/value
  extraction, and site emission for 16 added ALU classes: 64/32-bit immediate
  shifts, ADDW, bitwise immediate/register operations and register shifts.
  Uses existing `execute_*_char` lemmas; no new per-instruction hand proofs.

* Contract repair landed as `ef4e701` via `scripts/integrate.sh`; all gates
  passed after rebasing on A0-lib's decode table and A0-boot's runtime repair.
* First generated arm body: `Vsa.Sim.tr_const0`
  (`OCaml/Vm/Sim/Const0Segment.lean:20`) proves the three instructions from
  `0x800035c0` to the dispatch head. `const0_loaded`
  (`OCaml/Vm/Sim/Const0Pins.lean:8`) derives its code pins from the complete
  OCaml image. This is a machine segment, not yet a full `ArmSim.next` case:
  dispatch-to-body composition, runtime preservation, and the VM-data bridge remain.
* `scripts/gen_arm_pilot.py` composes the existing code-pin, site and segment
  generators using census boundaries and A0's per-word `ElfDecode` facts.
  It imports only the `SegSt` boundary record from syi; no Snprintf import
  closure is needed. Generated files and their spec are checked for drift.

* `run_sim`, `simOfArms`, `ocamlrun_refinement_of_arms` now carry the stronger
  relation throughout and still derive the unchanged headline.
* `forceExit_not_running` in `OCaml/Vm/Sim/Obstruction.lean` proves the old
  HTIF witness cannot satisfy the repaired relation.
* The five original obstruction results remain checked and audited:
  `repr_forceExit`, `forceExit_halted`, `forceExit_not_plus`,
  `armSim_not_repr`, and `loaded_not_armSim`. The last two now explicitly
  refer to `DataOnlyArmSim`, the legacy data-only loop contract, not the
  repaired production `ArmSim`.

## Dispatch table

`dispatchOffset_loaded` derives all 149 opcode table words from
`ExecutableImage.rodata`; `dispatchOffset_target` checks their signed offsets
against census targets. `dispatchOpcode_guard`, `dispatchTarget_aligned`, and
`dispatchTarget_clear` check the branch bound and indirect-jump geometry.
All are generated in `OCaml/Vm/Sim/DispatchTable.lean` and its seven chunks
by `scripts/gen_dispatch_table.py`, with data addresses from `Layout.jumpTable`.
Each literal byte is checked separately in the kernel; the full image is
never evaluated as one proposition. `dispatch_run` (`OCaml/Vm/Sim/Dispatch.lean:37`) composes the table with
`tr_dispatch`: from named `DispatchInput`, it reaches the selected arm in at
least eight machine steps. `DispatchPost` records its PC, advanced bytecode
pointer, unchanged memory, and complete frame outside x15/x23 and standard
step noise. `dispatchIndex*` discharge the table RAM/HTIF geometry.
The input retains explicit bytecode-address bounds/HTIF exclusion and tick
bounds, which `Running` does not yet supply; a full arm case is not claimed.

## CONST0 representation bridge

`const0_arm` (`OCaml/Vm/Sim/Const0.lean:14`) composes `dispatch_run` and
`tr_const0` through `StepsN.append`, then restores `Running` for the state
with PC advanced by one and accumulator zero. The payload uses the primitive
lane’s `VmPayload.accu_int` and `.frame`; complete register frames preserve
sp/env/extra and all fixed loop registers. `MemoryStable L.runtimeOk` supplies
the runtime frame, just as it does for the primitive summaries.

`ArmInput` (`OCaml/Vm/Sim/ArmInput.lean:11`) is a named, stronger entry;
`ArmInput.running` projects to `Running`. `ArmInput.of_repr` derives it from
`VmReprAt`, platform/loop facts, the fetched opcode, `CodeReadAt`, tick < 2,
and a non-cache opcode position (`methodCacheSlot ... = false`). The last
condition is needed because the landed F3 `CodeRepr` permits cache words to
vary. These remaining premises are explicit; neither `ArmSim.next` nor the
headline refinement is claimed or weakened.

## Shared immediate arms and NEGINT

`immediate_restore` and `immediate_preserved` in
`OCaml/Vm/Sim/Immediate.lean` package the restoration of VM data, fixed
registers, executable image and runtime from an `ImmediatePost`. CONST0 now
uses this shared rule. `negint_arm` (`OCaml/Vm/Sim/Negint.lean:12`) composes
its generated dispatch/body with the same rule, returning exactly the
`stepI` accumulator `untag (2 - tag64 n)`.

`tag_neg`, `untag_tag`, and `untag_neg` in `ImmediateArithmetic.lean` prove
modular negation and signed untagging for every 63-bit value. They reuse
`Primitives.tag_toNat`; no bounded-integer approximation or increased proof
limit is involved. Both arm bridges retain the documented `ArmInput` and
`MemoryStable` premises.

## Validation

* Shared restoration and refactored CONST0: 0.931s / 0.962s; 2.49s wall,
  1.96 GiB peak RSS. NEGINT arithmetic / arm: 0.952s / 1.0s; 2.58s wall,
  1.96 GiB peak RSS. Builds are separate and capped at 24 GiB.

* CONST0 representation bridge passes at default limits: ArmInput 1.0s,
  Const0 1.1s, combined 2.72s wall and 1.95 GiB peak RSS, under 24 GiB.

* Composed dispatch builds in 1.4s (2.29s wall, 1.93 GiB peak RSS).
  The extended table chunks build in 1.6–3.5s each, below 1.85 GiB.
  Generator headers disable implicit undeclared identifiers; literal index
  facts are checked separately and composed by opcode cases.

* Dispatch table chunks pass separately under 24 GiB at default limits:
  8.4s, 4.4s, 6.4s, 5.2s, 4.0s, 4.5s, 2.8s; peak process RSS below 1.86 GiB.
  Aggregate target lemmas build in 1.9s (2.68s wall, 1.82 GiB peak RSS).
  Generator drift, discipline, and abstraction checks pass.

* All six segment families pass after the pin-lookup change, each built
  separately under 24 GiB: CONST0 15s, NEGINT 15s, ISINT 6.6s, ACC0 13s,
  ACC 23s, dispatch 11s (shared-host wall timings). Peak process RSS stays
  below 1.86 GiB. Discipline, generator drift, and abstraction checks pass.

* Dispatch build passes under 24 GiB and default proof limits: code 3.7s,
  sites 9.6s, image projection 2.4s, segment 44s; wall 66.55s, measured
  user/system CPU 6.49/2.11s, peak process RSS 1.85 GiB. Shared-host
  scheduling affects these wall timings; no budget was increased.

* Framed body rebuilds, separately under 24 GiB, pass at default limits:
  CONST0 1.6s, NEGINT 2.0s, ISINT 2.5s, ACC0 1.0s, ACC 2.4s.
  Wall times 2.37–3.55s; maximum process RSS 1.85 GiB.

* Counted body rebuilds, one family per build under 24 GiB, all pass:
  CONST0 1.1s, NEGINT 1.2s, ISINT 1.4s, ACC0 1.3s, ACC 1.5s.
  Wall times 1.68–2.19s; maximum process RSS 1.85 GiB. Generator drift
  checks pass; no elaboration limit increased.

* ACC0 targeted build: code 0.884s, sites 0.907s, image projection 0.855s,
  segment 1.0s; wall 3.29s, peak process RSS 1.70 GiB.
* ACC targeted build: code 1.0s, sites 1.4s, image projection 1.3s,
  segment 1.8s; wall 4.79s, peak process RSS 1.71 GiB.
  Each family was built separately under 24 GiB at default proof limits.

* NEGINT targeted build passed under `MemoryMax=24G`, default Lean limits:
  code 4.8s, sites 3.7s, image projection 3.7s, segment 2.2s;
  wall 12.71s, maximum process RSS 1.69 GiB.

* Original obstruction landed as `ea1cc61`, log as `c87fb48`, through
  `scripts/integrate.sh` with all gates passing.
* Repair targeted build passed under `MemoryMax=24G`: image data 7.9s,
  platform 0.9s, refinement 1.0s, obstruction/regression 1.3s.
* `OcamlrunRefinement` definition compared byte-for-byte with its previous
  definition; unchanged. New headline results are in `OCaml/Audit.lean`.
* Full validation and landing use `scripts/integrate.sh`, including image
  generator drift, axiom, TCB and abstraction gates.

* CONST0 measured build: sites 5.3s, segment 6.6s (default limits).
  Image-byte projections use small `decide +kernel` computations; ordinary
  tactic `decide` hit recursion depth on the packed literal, with no need
  to raise limits. The successful pin module build is measured separately.

* ISINT measured build: code pins 1.4s, full-image projection 1.7s, sites
  1.9s, five-step segment 1.8s; wall time 6.27s, peak process RSS 1.70 GiB.
  One family per build; timing differences include shared-machine load.
* Python checks pass for reserved shift encodings, 5/6-bit shift widths,
  x0/repeated operands and read-before-write tracking. All artifacts regenerate.
* Additional ALU smoke sites are generated from real ELF instructions;
  their Lean build and axiom audit passed in the completed integration gate.
* Interpreter census after adapter: only AUIPC (69), indirect JALR (6), and
  LHU (1) remain unsupported by the site classifier (whole interpreter scope,
  not an F1 opcode count). No claim that classification alone proves arms.

## Open / next

Continue with one generated F1 family per measured build. No unconditional entry/next/halt arm, F1 refinement instance, or
machine `whileMin` result is claimed. `whileMin_bcSem` remains bytecode-level.

Next: extend generated arm families, then discharge dispatch and full
representation/frame bridges. Dispatch,
allocation fast path, primitive summaries, and the actual loop/entry machine
proofs remain open. A0 has repaired the nursery bounds via `runtimeLayout`; its remaining
boot `Loaded` assembly now exposes its remaining control/image/binding obligations. `L.runtimeOk` must
still be maintained by every generated arm.
