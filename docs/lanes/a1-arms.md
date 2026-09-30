# Lane a1-arms

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

## Open / next

Continue with one generated F1 family per measured build. No concrete entry/next/halt arm, F1 refinement instance, or
machine `whileMin` result is claimed. `whileMin_bcSem` remains bytecode-level.

Next is the shared shifts/addw/tagged-ALU generator adapter. Dispatch,
allocation fast path, primitive summaries, and the actual loop/entry machine
proofs remain open. A0 has repaired the nursery bounds via `runtimeLayout`; its remaining
boot ELF text mismatch is tracked in that lane's log. `L.runtimeOk` must
still be maintained by every generated arm.
