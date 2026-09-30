# Lane a0-boot

## Status

The exit criterion is **not met**. The foreman authorized a nonempty nursery
at the existing cut. `RuntimeOk` now has heap bounds, no pending work, and
an abstract free-list predicate; nursery allocations remain ordinary heap
blocks handled by `HeapRepr`. There is no empty-nursery proof obligation.

The foreman's prerequisite `.text` identity check **fails**: 7,484 bytes
across 5,954 instruction words differ between the pinned proof ELF and the
standalone `while_min` ELF. The second-layout path is stopped as instructed.
`results/boot/while_min-text.json` pins both ELFs, text hashes/sizes, and
first differences. No pinned ELF or a0-lib proof has been changed.

Both text sections start at `0x80000000` and have 340,352 bytes. Their hashes:

* proof: `640e8ba050c4bb318805158198ffca365fabf1586d90788ea2d3badc41a4a591`
* while_min: `b03f3b97a4bf8e1c2261a886a3e65763b7034977b873d0bac9da54eb4bf2ee40`

The first instruction itself differs: `auipc gp,0x68` versus
`auipc gp,0x65`; `_start` also embeds different BSS addresses. A second
symbol layout alone therefore cannot make the existing code facts apply.
`OCaml.Layout` currently contains only `runtimeOk`; `LoadedAt` and `VmRepr`
still refer directly to the generated global address constants.

## Defined and proved

* `OCaml/Vm/Runtime.lean:57`: `RuntimeOk` supplies minor-heap bounds,
  no pending work, and a named abstract `freeList` predicate.
  `runtimeLayout` (line 63) is the concrete `OCaml.Layout`.
* `OCaml/Vm/Runtime.lean:68`: `RuntimeOk.youngPtr_bounds`.
* `OCaml/Refinement.lean`: `Loaded.runtime`, the named accessor for the
  runtime part of the existing existential witness.
* `OCaml/Vm/Boot/WhileMinObservation.lean:30`: `bounds`; line 33:
  `noPending`; line 36: `nursery_not_empty`. These are facts about a small
  observed projection, not a certificate of a reachable Sail state.
  All are included in `OCaml/Audit.lean`.

At step **4,269,235**, the Sail trace gives `young_ptr = 0x80283ce0` and
`young_alloc_end = 0x80284000`: **800 bytes allocated**. Bounds hold and
`caml_something_to_do = 0`. This is now a documented observation, not an
obstruction. `startup_byt.c:575–578` promotes globals without resetting
`young_ptr`, and `caml_sys_init` allocates argv. Counting `oldify_mopup`
calls as minor collections is not evidence of an empty nursery.

## Tooling and evidence

`scripts/syi/gen_boot_witness.py ocaml-cut` now dispatches to
`scripts/boot_cut.py`. It reads generated offsets, checks the ELF's key
symbols against that layout, streams the ordered stores, and stops before
applying the second interpreter entry row's instruction. It observed
35,289 stores. Trace files stay in ignored `c/build/`; the compact
observation is `results/boot/while_min-cut.json` (includes ELF SHA-256).

`scripts/gen_boot_observation.py` emits the small kernel checks; stage a5
checks drift. `check_all.sh` applies the lane's 24 GB cap and available
memory check to both builds and audits.

Reproduce from the validation `while_min.elf` at `c/build/nostdlib/`:

```sh
python3 scripts/census.py --elf c/build/nostdlib/while_min.elf --json c/build/nostdlib/census.json
python3 scripts/gen_layout.py --elf c/build/nostdlib/while_min.elf --census c/build/nostdlib/census.json > c/build/nostdlib/Layout.lean
python3 scripts/syi/gen_boot_witness.py ocaml-cut --elf c/build/nostdlib/while_min.elf --layout c/build/nostdlib/Layout.lean --work c/build/boot-while-min
python3 scripts/gen_boot_observation.py results/boot/while_min-cut.json
```

The measured ELF was copied read-only from the original validation build
into this lane's ignored build directory. Its SHA-256 is
`d008c1189aa093505ac4d92e84e340f6467e65fd8d83eaf402ff810c0665d924`.
It is not the pinned `while.ml` ELF. For example, its `Caml_state` symbol
is `0x80067230`, while `OCaml/Vm/Layout.lean` has `0x8006a370`.
All these addresses were read from the ELF/generated layout, not invented.

Reproduce the ELF comparison (default mode deliberately fails on this pair;
`--check-pin` succeeds if the recorded mismatch is unchanged):

```sh
python3 scripts/check_boot_text.py --candidate c/build/nostdlib/while_min.elf
python3 scripts/check_boot_text.py --candidate c/build/nostdlib/while_min.elf --check-pin results/boot/while_min-text.json
```

## Open and next

1. `.text` differs: stopped and logged per foreman direction. The named
   fallback is relocating the embedded program after BSS; do not replace
   the pinned ELF without approval. Coordinate resulting addresses with
   a0-lib before consuming its code and decode facts.
2. Consume a1-arms' running-platform invariant repair through main; entry
   must establish the appropriate running state, intact code and entry
   registers. The cut is before interpreter prologue, so dispatch-register
   initialization belongs to the entry simulation.
3. Port the boot memory reflection dependency closure. The inherited
   generator's legacy commands still target WHILE ASTs and absent
   `Vsa.Sim.Boot.*`/`WriteLogRead` modules. Checking store-log effects alone
   does not prove Sail reachability.
4. Certify startup via generated function summaries/step tables and run-kernel
   composition, consuming a0-lib's landed allocator/stdio specs. No such
   specs are duplicated here. Summarize the primitive-lookup loop rather
   than kernel-evaluating 4.27 million Sail steps.
5. Prove the concrete entry's code, heap, globals, world, registers, runtime
   and `fillZero` facts, audit `Loaded`, then discharge the exit row.

## Validation

* Read COMMON, CLAUDE, PHASES, PLAN; ran the abstraction inventory.
* Ran census before layout generation; pinned generated layout is unchanged.
* Actual Sail trace reproduces the documented cut-step count.
* Targeted runtime and observation builds pass under `MemoryMax=24G`.
* The first progress commit `f328a83` passed all integration stages and landed.
* Updated nursery contract and ELF mismatch pin: integration gate pending.
