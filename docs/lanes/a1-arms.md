# Lane a1-arms

## Current status

The repair (`ef4e701`), CONST0 (`3229c53`), and ISINT/shared ALU adapter
(`7994562`, integration head `dac2c19`) have landed through
`scripts/integrate.sh`. The delayed integration completed successfully
when host memory recovered; all gates, including the 16 ALU smoke sites,
passed. NEGINT subsequently landed as `e2777bc` with all gates passing.
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
  full register/runtime frame; no `ArmSim.next` case is claimed.
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
  dispatch, the blanket register/runtime frame, and the VM-data bridge remain.
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

## Validation

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

Continue with one generated F1 family per measured build. No concrete entry/next/halt arm, F1 refinement instance, or
machine `whileMin` result is claimed. `whileMin_bcSem` remains bytecode-level.

Next: extend generated arm families, then discharge dispatch and full
representation/frame bridges. Dispatch,
allocation fast path, primitive summaries, and the actual loop/entry machine
proofs remain open. A0 has repaired the nursery bounds via `runtimeLayout`; its remaining
boot ELF text mismatch is tracked in that lane's log. `L.runtimeOk` must
still be maintained by every generated arm.
