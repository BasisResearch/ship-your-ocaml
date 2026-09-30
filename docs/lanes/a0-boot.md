# Lane a0-boot

## NEEDS KIRAN

The requested empty-nursery invariant does not match the measured second
`caml_interprete` entry. Choose between allowing a nonempty nursery at that
cut (recommended) and changing startup/the cut to establish an empty one.
This is a change to the explicit lane requirement, not a proof optimization.
The choice is pending; the exit criterion is **not met**.

At step **4,269,235**, the Sail trace gives `young_ptr = 0x80283ce0` and
`young_alloc_end = 0x80284000`: **800 bytes allocated**. Bounds hold and
`caml_something_to_do = 0`. The kernel checks facts about these small
observed literals and proves a conditional `not_loaded`; it does **not**
yet certify the execution from `_start` or the observed projection.

The source agrees with the observation: `startup_byt.c:575–578` calls
`caml_oldify_one`, `caml_oldify_mopup`, then `caml_sys_init`. Promotion of
the globals does not reset `young_ptr` (`minor_gc.c:296–348`); the reset
belongs to `caml_empty_minor_heap`, and `sys.c:460` allocates `main_argv`.
Counting `oldify_mopup` calls as minor collections in `sail_run.py` is not
evidence of an empty nursery.

## Defined and proved

* `OCaml/Vm/Runtime.lean:57`: `PromotedRuntimeOk` supplies minor-heap
  bounds, the requested empty-nursery equality, no pending work, and a
  named abstract `freeList` predicate. `promotedLayout` (line 64) is the
  concrete `OCaml.Layout`; no arbitrary `True` free-list instance is used.
* `OCaml/Vm/Runtime.lean:70`: `not_promotedRuntimeOk_of_projection`.
* `OCaml/Refinement.lean`: `Loaded.runtime`, the named accessor for the
  runtime part of the existing existential witness.
* `OCaml/Vm/Boot/WhileMinObservation.lean:30`: `bounds`; line 33:
  `noPending`; line 36: `nursery_not_empty`; line 40: `not_promoted`;
  line 45: `not_loaded`. The last two require an explicit machine
  projection equality. All are added to `OCaml/Audit.lean`.

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

## Open and next

1. Resolve the nursery requirement. A changed invariant must also account
   for the running-platform invariant obstruction landed by a1-arms.
2. Align the program image and layout: either instantiate all representation
   addresses for the measured ELF, or embed while_min while preserving the
   pinned runtime addresses. Do not call the current observation a witness
   for the pinned layout.
3. Port the boot memory reflection dependency closure. The inherited
   generator's legacy commands still target `while-riscv-htif.elf`, WHILE
   ASTs, and missing `Vsa.Sim.Boot.*` modules; `WriteLogRead` is also absent.
   Checking store-log effects alone does not prove Sail reachability.
4. Certify startup via generated function summaries/step tables and run-kernel
   composition, consuming a0-lib's landed allocator/stdio specs. No such
   specs have landed yet in the main revision inspected; none are duplicated
   here. `strcmp` lookup accounts for most startup instructions, so summarize
   that loop rather than kernel-evaluating 4.27 million Sail steps.
5. Prove the concrete entry's code, heap, globals, world, registers, runtime
   and `fillZero` facts, audit `Loaded`, then discharge the exit row.

## Validation

* Read COMMON, CLAUDE, PHASES, PLAN; ran the abstraction inventory.
* Ran census before layout generation; pinned generated layout is unchanged.
* Actual Sail trace reproduces the documented cut-step count.
* Targeted runtime and observation builds pass under `MemoryMax=24G`.
* Hole and discipline checks pass. Integration gate pending on this commit.
