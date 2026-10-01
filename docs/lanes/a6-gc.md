# Lane a6-gc

## Status

G2 remains open. `Fits` still measures total allocated words; no claim that
the one-line ocamlc run is covered by G2.

## Checked progress

- `OCaml/Vm/Reloc.lean:434` `vmReprAt_reloc`: all fourteen current
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
- Integration gate result will be recorded after running scripts/integrate.sh.
