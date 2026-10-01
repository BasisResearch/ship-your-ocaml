# Lane a6-gc

## NEEDS KIRAN

Choose the G2 specification repair for observable Forward short-circuiting:
add a semantic GC-safety precondition excluding observations that distinguish
a Forward block from its payload, or revise BcSem/refinement to model those
GC-visible changes. A transparent value relation alone is insufficient.
`python3 scripts/check_gc_forward.py` runs the pinned host OCaml 4.14.4 and
checks `false true` for ISINT before/after a minor collection. A question is
pending in the lane session; independent interfaces and checks continue.

## Status

G2 remains open. `Fits` still measures total allocated words; no claim that
the one-line ocamlc run is covered by G2.

## Checked progress

- `OCaml/Vm/Reloc.lean:455` `vmReprAt_reloc`: all fourteen current
  `VmReprAt` fields transport via Eqv from the named `VmImage` interface.
  Adds optional-value register, general observation, and fixed-code-base
  combinators; channels, console, code and trap metadata are covered.
  This proves conditional representation transport, not collector execution.
- Reuses a1's `platformEqv` / `loopRegistersEqv` in
  `OCaml/Vm/PlatformReloc.lean` for the separate running-platform fields.
- `abstractions/round1/check_laws.py`: executable oldify/mopup model with
  zero-header forwarding, special-tag guards, no-scan copies and infix
  offsets. 42 Forward cases and 12 valid infix cases pass; both root orders
  exercise already-forwarded blocks. Original 20,000-trial laws still run.
- `lake build OCaml.Vm.Reloc` passes under the 24 GB cap. Headline theorem
  added to `OCaml/Audit.lean`.

## Obstructions and next steps

- Real Forward short-circuiting returns tagged integer 85 for a young
  Forward block containing integer 42. Strict `ObjAt` demands a Forward
  header at the new address; this is not a relocation of the old object.
  The Python law check asserts the counterexample. Supply a checked lax
  relation and its compatibility with bytecode observations before claiming
  the collector establishes `VmImage`.
- A pointer to field 2 without an Infix header is treated as a separate
  object by the runtime; the law check asserts failure of affine relocation.
- Next: concrete suppliers for the named safety/barrier interfaces; partial
  relocation invariant; generated machine CFG/segments and MachWP loops.
  Nursery bounds must permit the observed 800 allocated bytes at startup.
- `scripts/gc_cfg.py --check` / `results/gc-cfg.json`: gen_fn accepts oldify
  (145 instructions, 38 blocks), but does not recognise its loop template.
  Its `Vsa.Sim.DeriveCaseRow` dependency is now ported. Mopup is rejected
  for 29 branches (>20); empty_minor_heap for 205 instructions (>150).
  Do not raise those budgets; generate collector code pins and split into
  meaningful machine segments/routes with named loop invariants.

## Additional checked results

- `OCaml/Vm/Gc/Forward.lean:19` `forwardValue_int`, :25
  `forwardValue_not_isInt`, :36 `scanCoherent_forward_int_obstruction`, :51
  `forward_objAt_obstruction`: kernel-checked obstruction to the strict
  bridge and to unrestricted ISINT preservation by a transparent Forward
  value relation. The relation is a candidate for testing, not adopted as
  production VmRepr and not claimed to capture every C guard.
- `OCaml/Vm/Gc/Invariant.lean:52` `LoopHead`: named safety fields, with no
  empty-nursery assumption. :68 `WritingArmBarrier` supplies the requested
  interface for a1's writing-arm summaries. :75 `LoopHead.running`, :81
  `rememberedComplete_empty`, :89 `LoopHead.reloc` are proved. The ghost
  remembered list still needs linkage to the concrete ref_table; these
  definitions do not assert that existing ArmSim supplies the safety facts.
- `OCaml/Vm/Gc/Budget.lean:36` `liveWords_le_allocated`, :41
  `fitsLive_of_fits`: G1 implies the candidate FitsLive bound. Production
  Fits remains unchanged. Minor promotion alone is not major reclamation.
- `python3 scripts/check_gc_forward.py`: pinned host 4.14.4 prints exactly
  `false true` across Gc.minor. This is runtime evidence, not a Sail proof,
  and not a proof that this Obj/Gc test is inside the present BcSem fragment.
- Targeted Lean builds for Reloc, Gc.Forward, Gc.Invariant and Gc.Budget
  pass under the 24 GB cap. All new theorem names are in OCaml/Audit.lean.
- The Python law checker now asserts the positive laws and expected
  negative controls instead of merely printing counts.

## Landing

- `2ef2a72` landed on origin/main with scripts/integrate.sh (exit 0).
- `f29a381` (obstructions/interfaces/budget) and `4f26d45` (census)
  landed on origin/main with scripts/integrate.sh (exit 0). A push race
  with the NEGINT lane was resolved by retaining both import/audit lists;
  the complete gate was rerun successfully after the rebase.
- New headline theorem axiom audit passed; no nonstandard axioms. The
  refreshed abstraction census passes: C3 has 7 proofs since adoption.
- Log-only landing follows these checked commits; no proof claim changed.
- Exit remains unmet: no oldify machine loop proof, no lax bridge compatible
  with all admitted observations, no production live-word Fits, and no
  one-line compiler Layer A budget theorem. The specification question at
  the top blocks the Forward-sensitive proof; generation/reclamation gaps
  remain explicit rather than being assumed away.


## Fixed-address .embed migration preparation

- Foreman notice received: .text entry addresses stay fixed, but data symbols
  and gp/auipc-relative instruction immediates move. Concrete data references
  in this lane use `OCaml/Vm/Layout.lean`; no hard-coded ELF data address was
  found. Numerical addresses in the Forward counterexample are synthetic
  witness addresses, not runtime symbols.
- `scripts/gc_cfg.py` now records the pinned ELF SHA-256 and the exact
  little-endian instruction SHA-256 for each collector function. CFG-only
  comparison could miss changed immediates with unchanged control flow.
- Current migration status: not yet present on origin/main at c7989c8.
  After the a0 landing: rebase, run `python3 scripts/gc_cfg.py >
  results/gc-cfg.json`, then `python3 scripts/gc_cfg.py --check`, rebuild
  the lane modules under the memory cap and run scripts/integrate.sh.
  Layout/decode/code-pin regeneration is owned by a0's migration landing.
- Independent progress: `oldify_special` in the law checker now uses the
  actual intrusive queue representation (source header 0, source field 0
  points at copy, copy field 1 points at next source). It removes a queued
  source before recursive scanning, matching minor_gc.c. The queue invariant
  is checked after each recursive oldify and each mopup scan.
- Validation: 2,000 generated cyclic/aliased heaps under two root policies
  (single root and all roots) satisfy queue invariants, exact reachable-set
  forwarding, injective destinations, final typed payloads, and preservation
  of unreachable sources. Existing Forward/Infix and 20,000-trial law checks
  still pass. This is executable-model validation, not a machine proof.


## Remembered-set store rule

- `OCaml/Vm/Gc/Barrier.lean`: `slotComplete_store` proves completeness
  across a field update from the named `BarrierEffect` (old scanned-slot
  frame, retention of existing table entries, insertion on the newly-young
  branch). The old-young early return uses PRE-state completeness.
- `rememberedComplete_of_slots` supplies the typed `RememberedComplete`
  interface from the stronger invariant over a fixed set of all old scanned
  slots. Representation and slot-coverage hypotheses remain explicit.
- This is the reusable logical half of caml_modify, not its machine run.
  Darkening major-heap headers, concrete ref-table linkage/growth and new
  allocation slots remain separate obligations. Header and table writes are
  intentionally outside the scanned-slot frame. There are no data addresses
  in the rule, so the .embed migration does not affect its statement.
- 14 exhaustive abstract classifier/table-membership cases pass; the
  missing-pre-completeness negative case demonstrates why old-young early
  return cannot repair an already incomplete table.


## Generated-row adapter

- `Vsa/Sim/DeriveCaseRow.lean:35` `segToTriple` ports the existing generic
  adapter from ship-your-interpreter (provenance in ATTRIBUTION.md). It
  reuses segEval_sound and uses a named-field SegPre. No instruction is
  hand-stepped, no concrete address is introduced, and no heartbeat setting
  is raised. `lake build Vsa.Sim.DeriveCaseRow` passes under the 24 GB cap.
- The collector report is regenerated with the now-resolved import
  dependency. This does not claim generated collector machine rows, code
  pins, loop summaries, or call contracts are discharged.
- `8d4c9ac` (queue-law checks / fingerprints) and `edec486` (logical
  remembered-set barrier rule) landed using scripts/integrate.sh (exit 0).


## Promotion footprint corrections

- `Eqv.wordView` observes only the relevant parts of a memory word;
  `objEqv` now uses tag/size (`headerView`) rather than requiring a verbatim
  header copy. `headerView_color` proves that all four color encodings
  preserve tag and size when the header fits in 64 bits.
- `ObjMoved`, `objAt_reloc`, and `payload_copyIn` now require exactly
  `8 * o.wosize` payload bytes, not an extra word. Existing transport proofs
  still use Eqv; this strengthens the usable transport theorem by weakening
  its image premises to what the real collector supplies.
- Source: `memory.c:caml_alloc_shr_aux` chooses white/black when promoting;
  `minor_gc.c:caml_oldify_one` copies precisely Wosize payload words.
  Python checks exercise both allocation colors and an absent next word;
  cyclic queue tests also vary the allocation color. The law checker and
  targeted Reloc/Invariant/Barrier builds pass.


## Generated collector rows

- `scripts/gen_gc_rows.py` prepares oldify-one (57 arms) and caml_modify
  (29 arms) using gen_fn, the pinned ELF, and the generated decode table.
  Every generated postcondition is a named-field structure, retaining
  computed registers, tick bound and instruction-counter existence. Calls stop at
  their call sites; these are segment proofs, not whole-function summaries.
- The generated audit enumerates all 387 row, segment and code-pin
  declarations. The capped build of `OCaml.Vm.Gc.Generated.Audit` passes,
  and a separate capped Lean audit exits 0 with exactly those declarations
  and only the three permitted standard axioms.
- Reproduce the bundle with `python3 scripts/gen_gc_rows.py` and check
  with `--check`. The strengthened postconditions pass the capped build
  (554 jobs). The full gate imports the generated audit and checks both
  row/code generation and CFG fingerprints. After the pending image
  migration reaches main, regenerate both this bundle and
  `results/gc-cfg.json` from their generators.
- The header/payload correction passed the full gate; the push raced
  with a1 dispatch work. Rebased keeping both audit additions. The
  correction and generated rows are proceeding through integration together.
- Concrete data addresses continue to come from Layout; instruction words
  and code addresses come from the pinned ELF/decode generators.
