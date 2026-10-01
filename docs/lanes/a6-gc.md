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

- `OCaml/Vm/Reloc.lean:436` `vmReprAt_reloc`: all fourteen current
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
- Next: named NoForgery/RememberedComplete and barrier interfaces; partial
  relocation invariant; generated machine CFG/segments and MachWP loops.
  Nursery bounds must permit the observed 800 allocated bytes at startup.
- `scripts/gc_cfg.py --check` / `results/gc-cfg.json`: gen_fn accepts oldify
  (145 instructions, 38 blocks), but does not recognise its loop template.
  Its emitted rows import absent `Vsa.Sim.DeriveCaseRow`. Mopup is rejected
  for 29 branches (>20); empty_minor_heap for 205 instructions (>150).
  Do not raise those budgets; port the missing generator dependency and
  split into meaningful machine segments/routes with named loop invariants.

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
