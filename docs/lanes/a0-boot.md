# Lane a0-boot

## Round 2 status (2026-10-04)

`Startup/TableZeroed.lean:25` closes `reset_table_zeroed_exists`: the actual
pinned-image reset now returns from the first 56-byte table's native memset.
`ResetTableZeroed.zero_bytes` (`:37`) proves all 56 bytes are zero.
`TablePublished.lean:38` closes the preceding domain-field publication;
`TablePublish.lean:115` proves the shared source protocol for all three table
slots, using generated Layout offsets. `TableZero.lean:55` composes both
ordinary zero-call sites with the complete memset summary. `TableReturn`
recovers the allocator's executable image, saved domain registers and fresh
block geometry. A local total-byte word observation helper transports
`Caml_state` across the allocator footprint. The final reset composition
checks in one second.

The complete memset increment landed as `6d2ebce`, full gate passed.
Next: retain the written-register interface needed for full library
well-formedness after zeroing, carry allocator capacity and publication
through that effect, then compose the remaining two allocations/zeroing and
the domain epilogue. Round 2 reset-to-cut/Loaded exit remains open.


`Startup/Memset56.lean:50` closes the complete native aligned 56-byte
`memset` summary for any allocation in the arena. It composes the generated
entry, generic word-pair loop, computed byte-tail dispatch and eight byte
stores/return. `MemsetReadback.lean:25` and `:35` prove all outside bytes
unchanged and every byte of the requested extent zero. The exact effect,
full register/output frame, executable image and platform are retained.
`MemsetTail.lean:13` and `MemsetBytes.lean:56` are the reusable tail pieces.
The summary and readback check in 1.4 s and 1.2 s. The generic loop increment
landed as `f8936b6`, full gate passed.

Next: publish the first returned table pointer and supply the new memset
summary, preserving allocator credits, then repeat for the other two tables
and return through the domain epilogue. Reset-to-cut remains open.


`Startup/MemsetPrefix.lean:65` proves `memset56_prefix`, selecting the
aligned 56-byte zeroing path. `MemsetPair.lean:60` proves `memset_pair`,
including both word stores and the native loop branch. `MemsetLoop.lean:66`
proves `zero_pairs` for an arbitrary pair count using `loopFromBody`, with
exact `clearWords` memory effect, executable image, platform and register
frames. Geometry derives write windows from the allocator arena bounds.
The loop module checks in under one second; no machine-step replay or
budget increase. Generated regions reuse the existing library memset pins.
The eight-byte tail and composition with the actual first table allocation
remain next; reset-to-cut and Round 2 exit remain open.

The first table malloc return increment landed as `3550f1f`, full gate passed.

## Prior reset frontier (2026-10-03)

`Startup/TableAllocation.lean` closes `reset_table_allocation_exists`: actual
reset returns from the first 56-byte minor-table malloc, with a fresh aligned
block, the original domain allocation retained, and remaining allocator
credits. It consumes `allocator_summary` without any new allocator execution
proof. `TableAllocatorInput.lean` transports the library platform, read-only
pins and capacity through the saving prefix and disabled-pool tail wrapper.
`PoolFrame.lean` proves the pooling switch remains zero through both the
initial malloc and subsequent startup writes. Shared `lpins8_observed`
transports total scalar pins; the existing write-log pin helper now reuses it.
The allocator-input and allocation modules check in 1 s and 2 s.

The first table-request prefix landed as `59e520d`; its generated code-pin
file was accidentally omitted from that commit and landed immediately as
`d00cb44`, full gate passed. The generated dependency set is now complete.
Next: publish the table pointer, prove its memset zeroing, then compose the
remaining two table allocations and domain epilogue. Round 2 exit is open.


`Startup/MinorTablesPrefix.lean` closes `reset_table_alloc_exists`: the
actual reset reaches the first 56-byte minor-table stat-allocation request.
`minorTables_prefix` and `minorTables_allocate` certify the source stack
saves, reloaded domain pointer, argument and call, retaining the exact
write log and full nonwritten-register frame. `domainInit_domain_word`
reads back the prior published pointer using the shared write-log rule.

A combined raw-instruction access proof hit kernel recursion. Separating
code/access certificates with `AccessPlan` and consuming generated literal
instructions (`minorTablesSave_eq`) resolves it without raising budgets;
the complete prefix module checks in 2.4 s. All addresses derive from the
pinned instructions and generated Layout.

The allocator-capacity increment landed as `a59f2de`, full gate passed.
Next: preserve allocator inputs and the disabled-pool test across the
prefix, apply `allocator_summary`, and summarize the following memset and
two further allocations. Reset-to-cut execution remains open.


`Startup/DomainHeap.lean` now supplies allocator capacity, the complete
`VsaOk` platform invariant, and all allocator read-only pins at the actual
minor-table call. `FirstMallocEnd.room` retains any credit bound justified
by `top <= heapStart + 944`; `domainInit_log_inside` confines the following
stores to the domain payload and publication word. The landed
`RegistersPost.vsaOk`, `frameOn_writeLog` and `roomLocal_vsaRoomB` transport
these invariants without reproving allocator behavior.

`Startup/AllocatorRun.lean` (`allocator_summary`) bridges the landed
`mallocChgRun_proved` to `FnSummary` for arbitrary later startup requests,
with fresh non-null allocation and remaining credits. `allocator_separate`
and `allocator_stack_disjoint` cover any startup stack above the heap.
The initial-domain increment landed as `9ec0c5e`, full gate passed.
Next: generate and compose the minor-table allocator's three 56-byte
allocations and zeroing calls, then finish domain initialization. The
full reset-to-cut run remains open.


`Startup/DomainInit.lean` now closes `reset_minor_tables_exists`: actual
reset reaches `caml_alloc_minor_tables` after publishing the first allocated
domain and performing the source's thirteen minor-heap field zero stores.
The exact write log comes from generated instructions; `domainInit_log`
normalizes the reloaded pointer via the generic `published_word` rule.
`domain_initialize` / `domain_init_tables` preserve the executable image
and full nonwritten-register frame. `MallocReturn.lean` recovers their
optional-register interface from the library model's total observations.
The domain summary checks in 17 s without evaluating a machine run.

The first-allocation increment landed as `b555d0c`, full gate passed.
Next: retain the allocator capacity bound across domain payload writes,
then summarize minor-table allocation and finish the domain initializer.
Subsequent runtime startup and the Round 2 exit remain open.


`Startup/MallocRun.lean` now closes `reset_first_allocation_exists`: the
actual pinned ELF reset reaches the return from its first 928-byte malloc.
`ResetMallocWitness.malloc_run` instantiates the complete bootstrap proof
with loader-supplied allocator pins, crt0's retained global pointer, dense
RAM presence, exact stack geometry, and a disjoint mutable footprint.
`FirstMallocEnd` records return PC/ABI, the exact pointer `heapStart + 16`,
and the initialized heap shape. The shared library `malloc_ret` supplies
its terminal rule; its impossible failure branch is rejected by capacity.
The symbolic-to-machine bridge uses `symbolic_summary` and the run kernel.
The final bridge module checks in 1 s, without evaluating the execution.

The image increment landed as `356d713`, full gate passed. Next: recover
the generated-block interface after malloc, finish domain initialization,
and continue the remaining runtime startup calls. Round 2 exit remains open.


`Startup/AllocatorImage.lean` (`ResetMallocWitness.allocator_loaded`) now
supplies the entire landed allocator read-only table at the actual first
call. `gen_boot_allocator_pins.py` certifies 366 bounded chunks against the
executable image and the loader's `_impure_ptr` word; the existing balanced
append tree assembles them. This checks in 11 s without evaluating the
memory map. `AllocatorByteSource.geometry` places every pin in RAM, below
the heap, outside mutable allocator globals. `initial_byte` transports any
untouched pre-BSS byte through the complete startup prefix. The generator
is checked by stage a5.

The full-platform increment landed as `367e880`, full gate passed. Next:
instantiate ownership and the return predicate, apply `symbolic_summary`,
and extend the actual reset witness through the first malloc. Runtime
startup after that return and the Round 2 exit remain open.


`Startup/MallocPlatform.lean` (`ResetMallocWitness.vsaOk`) now supplies the
library's full platform invariant at the actual first malloc: `GoodState`,
valid tick, all 31 GPRs present, RAM presence for any contained live footprint,
and zero HTIF payload-write counter. The reset proof now retains that source
counter, and the crt0/main summaries retain GPR presence through generated
blocks, the BSS loop and calls. Shared `GprPresent` rules combine finite output
pins with complete frames; no per-register machine stepping is introduced.
The domain/stat-allocation interfaces now retain x15's observed zero value,
which their previous projected interfaces dropped. The platform module checks
in under one second.

The complete first-malloc increment landed as `1c3066c`, full gate passed.
Next: allocator text/read-only pins and ownership instantiation, then use
`Primitives.symbolic_summary` to extend the concrete reset witness through
malloc. Subsequent runtime startup and the Round 2 exit remain open.


`Startup/MallocBootstrap.lean` now proves the complete first allocator call:
`malloc_bootstrap` consumes the initial arena, and `malloc_bootstrap_entry`
includes the public malloc wrapper. After initialization it uses the landed
`ext_stats`, `PHeapAt.topResize` (unchanged break), and `ext_top`/`top_split`
proofs; it does not duplicate the normal allocation/split implementation.
`MRet.first_pointer` derives the exact returned pointer `heapStart + 16`
from the library's aligned allocation and top bound. The module checks in
1.1 s. The initialized-heap increment landed as `d025bb3`, full gate passed.

Next: instantiate the symbolic contract at `ResetMallocWitness`, using the
existing `Primitives.symbolic_summary` bridge. The remaining platform inputs
are complete GPR presence and the idle HTIF payload counter at the first
call; RAM presence and initial allocator metadata are already closed.
Then continue domain initialization and subsequent startup. The complete
reset-to-cut run and Round 2 exit remain open.


`Startup/MallocBootHeap.lean` (`malloc_boot_initialize`) now composes the
first malloc prefix, both morecore summaries, and source top initialization.
It reaches the statistics pass at `0x800379e8` with ordinary `PHeapAt`:
top `heapStart`, page-aligned break `heapStart + 3776`, header 3777,
zero binblocks and all 127 empty bins. Saved registers, memory outside the
malloc ownership window, and byte presence are retained. Its inputs are
`InitialArena`, the 928-byte request, stack/ownership geometry and no prior
allocations; it does **not** assume an initialized heap.

`MallocBootAligned.lean` consumes the landed `sbrk_r_run` for the second
2800-byte request. `MallocBootTop.lean` certifies the three initialization
stores. `AllocatorFresh.lean` assembles the empty arena into `PHeapAt`, and
`malloc_boot_fresh` supplies its fields from both call frames and the exact
logs. A direct header-bit rewrite hit kernel recursion while unfolding a
symbolic read; the generic option-word lemma checks without raising limits.
Shared `malloc_morecore_pre`, `malloc_sbrk_window` and `morecore_spill_value`
avoid repeating call geometry, ownership and spill recovery.

Next: consume existing `ext_stats`, `ext_top`/`top_split` to finish malloc,
bridge its SWP contract to the actual reset witness, then continue startup.
The complete reset-to-cut run and Round 2 exit remain open. The preceding
first-morecore/alignment increment landed as `b8041a0`, full gate passed.


`Startup/MallocBootMorecore.lean` (`malloc_boot_morecore`) now composes the
first malloc prefix with `_sbrk_r`'s bootstrap summary. The zero-break and
ownership preconditions are discharged from `InitialArena` and the exact
call log. Its return has `a0 = heapStart`, break `heapStart + 976`, preserved
malloc frame and spills, and word/presence frames. `MFrame.after_sbrk`
shares the nested-call frame transport.

`Startup/MallocBootAlign.lean` (`malloc_boot_alignment`) checks the source
path from that return through mallinfo update, sbrk-base initialization and
the second `_sbrk_r` call. The request is 2800 bytes (page padding computed
from generated `heapStart`), with an exact ten-store log and preserved
saved registers. It reuses the generic spill/read certificates and generated
allocator steps. Next: second call, top initialization/split, `HeapAt`, and
the remaining startup summaries. Full reset-to-cut remains open.

The first malloc prefix landed as `aaad58e`, full gate passed.

`Startup/MallocBootPrefix.lean` now proves `malloc_boot_prefix`: starting
from the actual first request (928 bytes) and `InitialArena`, the generated
allocator steps round the request to 944, search the empty bins, inspect
the dummy top and sentinel, then reach `_sbrk_r` with a 976-byte request.
`MallocBootAtCall` retains the exact eight-store native frame log and saved
registers. Four `#ix_piece` proofs compose with `#ix_chain`; the complete
prefix checks in about seven seconds with only standard axioms. No
initialized heap premise is used. Next splice `sbrk_r_boot`, prove the
second alignment call, initialize/split the top, and establish `HeapAt`.
The reset-to-cut exit remains open.


Current frontier: actual reset reaches the first malloc entry (`bfcd9da`,
full gate passed). `Startup/AllocatorInitial.lean:39`
(`ResetMallocWitness.initial_arena`) now supplies its source initial
metadata: zero break, dummy top, -1 sbrk-base sentinel, zero statistics,
and all 127 empty bins. `AllocatorReads.lean` transports bounded word
certificates and proves RAM presence through the startup effects; it also
turns every complete BSS word into the allocator's zero `read64` fact.
`gen_boot_allocator.py` emits 256 eight-byte loader certificates and checks
in 3.3 s. An initial unchunked 127-index assembly hit default recursion depth;
shared `emit_finite_family` now assembles finite chunks without a budget change.
Stage a5 checks the new generator.

`Startup/SbrkBootstrap.lean:15` (`sbrk_r_boot`) proves the first successful
`_sbrk_r` call, using the landed allocator instruction table and `sx_run`.
It takes the actual zero-break branch, returns `heapStart`, advances the
break by the request, restores the native caller registers, frames memory
outside `SbrkW`, and preserves byte presence. It checks in 4.5 s. Its
`SbrkBootPre` requires only ordinary call geometry/ownership and enough
room; the single source initialization store supplies the usual break
read. This does not yet prove first malloc: next compose malloc's empty-bin
path, the two morecore calls, top initialization and split, establish
`HeapAt`, then consume the general allocator contract. Full reset-to-cut
and the Round 2 exit remain open.


The prefix/bootstrap-obstruction increment landed as `a6de181`, full gate passed.

The next composition now checks: `WhileMinFirstCall.reset_domain_exists`
and `WhileMinToMalloc.reset_malloc_exists` are closed witnesses from the
actual parsed ELF reset through the first malloc entry, carrying the source
928-byte allocation request, stack and return link. The reset setup proves
all 31 GPRs begin at zero. crt0/main retain the full nonwritten-register
frame already supplied by generated blocks and the BSS loop; this discharges
x9 without a new premise. `BlockPost.frame_subset` shares finite write-set
inclusion, and `lpins8_writeLog` transports the domain/pool load certificates
past the three native stack saves. These modules check in under two seconds.
First malloc bootstrap, the rest of domain initialization, and subsequent
startup remain open; the lane exit is not met.

Latest checked increment: `Startup/CamlMainPrefix.lean` (`caml_main_domain`)
and `Startup/DomainPrefix.lean` (`domain_allocate`) prove the generated
first runtime call and fresh-domain allocation prefix. They retain exact
store logs, untouched-register frames, image, output and platform facts;
the actual JAL supplies the return link. `PrefixCall.prefix_call_post`
shares the composition rule. Generator-produced literal instruction
certificates keep symbolic evaluation bounded. The store-log proof initially
expanded symbolic `toNat` arithmetic until the memory cap/recursion limit;
explicit instruction simplification and separate bitvector address equalities
now check both complete prefix modules in about one second, with no budget
increase.

`Startup/BssFrame.lean` transports byte reads and executable image through
crt0/main and supplies `CrtCamlMainPost.leaf`. Generic `loaderMem_bytes` and
`bytesT_local_eq` reuse the bounded byte-view API. `AllocatorBootstrap.lean`
proves `ResetCamlMainWitness.sbrk_base` is the actual loader sentinel -1,
and `ResetCamlMainWitness.heap_not_initialized` excludes every instance of
the landed allocator's `HeapAt` predicate at C entry. This is a checked
obstruction to applying `malloc_all` prematurely. Next: preserve the needed
reset register frame through these prefixes, prove first-malloc bootstrap,
then consume the existing general allocator contracts. No user decision is
needed. The complete reset-to-cut execution and Round 2 exit remain open.


The reset-to-cut execution proof is now the active exit criterion. Round 1
proved only `Loaded` for the complete captured cut; the native run is not
a substitute for a kernel execution theorem.

PMP reset landed as `d6760e8` after the full gate passed. It is checked in `Startup/ResetPmp.lean`: `reset_pmp_run`
proves the actual source loop leaves the complete machine state unchanged
when `pmpcfg_n` is the initializer's zero vector. `Vsa.Sim.Stays.forIn`
reuses `Vsa.Densify.forIn_range_of`; its body proof works for every index,
including out-of-bounds vector accesses, without replaying 64 iterations.
`writeReg_present` supplies the reusable idempotent register-write law.
The complete architectural reset and ELF setup landed as `f526441` after the full gate passed:

* `reset_tvecs_run` (`Startup/ResetTvec.lean`) preserves the zero trap vectors.
* `reset_misa_effect` (`Startup/ResetMisaEffect.lean`) turns the existing
  ISA summary into one exact register update, using `Vsa.Sim.state_eq`.
* `reset_sys_run` (`Startup/ResetSys.lean`) composes the system-reset source,
  preserving memory/output/cycles and registers outside `sysResetWrites`.
  A broad `simp_all` frame proof exceeded default heartbeats. The replacement
  uses `register_insert_frame` and finite footprint membership certificates;
  the complete module checks in 2.7 s without a budget increase.
* `initializer_host` proves the source-derived register tail preserves the
  ELF's HTIF header. `RunnerSetupPost.host` now carries those exact pins.
* `reset_run` and `init_model_run` (`Startup/ResetPlatform.lean`,
  `Startup/InitModel.lean`) establish all of `GoodState`, through hart,
  system, TLB and landing-pad reset and configuration validation.
* `setupElf_run` (`Startup/SetupElf.lean`) proves complete Sail setup for any
  ELF with the pinned tohost metadata. It preserves loader memory and output,
  increments cycle count once and sets the ELF entry PC. `elf_reset_exists`
  constructs a step-zero `ElfResetReady`; `ElfReset.ready` gives these facts
  for every successful reset. `whileMin_reset_exists` specializes to the
  named `WhileMinElf` metadata/loader contract, whose supplier is still open.

The reset-to-C-entry increment landed as `4565641`, full gate passed.
`reset_to_caml_main` (`Startup/ResetToCamlMain.lean`) proves actual
machine steps from `fillZero` of an `ElfReset` configuration to `caml_main`.
Its `WhileMinElf` premise describes only loader bytes and metadata; platform
and code premises are discharged. `gen_startup_rows.py` reuses
`gen_arm_pilot.image_projection` for the crt0, main and primitive-table code
pins; all three projections check from the fixed executable image. The
result carries exact BSS/main memory effects, argv, stack/link and output.

The generic loader correspondence landed as `5b690cc`, full gate passed, in `Vsa/Sim/Boot/LoaderPiece.lean`
and `LoaderPieces.lean`. `loadPiece_eq` proves the actual byte-array fold
(including its duplicate-address check) equals `insertRange` on a fresh
range. `initializeMemory_pieces` factors the frozen source definition;
`initializeMemory_eq` composes arbitrary disjoint pieces into `loaderMem`.
The proof uses abstract array/list induction, not a concrete memory-map
computation. Both modules check in under one second each. Concrete parsed-ELF
piece geometry and byte-view certificates must still instantiate the theorem.

The bounded-header increment landed as `d29b321`, full gate passed.
The exact 515,920-byte while_min ELF is archived under its existing SHA256
pin (`results/boot/while_min-elf.bin.gz`). `gen_boot_elf.py` verifies that pin
and the emulator's archived pieces, reuses `WhileMinImage.imageByte` for
loader-covered ranges, and emits only the remaining file bytes as sparse
packed pages. The page emitter is shared with `gen_boot_image.py`; its old
output is unchanged. Stage a5 checks both generators.

`Vsa/Sim/Boot/ByteView.lean` proves size, reads and slicing for bounded byte
views. `ElfHeader.lean` proves the real header parser observes only 64 bytes.
`WhileMinElfHeader.source_header_parse` proves that the exact full file parses
to its generated header, and `header_entry` agrees with pinned Layout.
Direct header simplification tried to expand the full array (one owned
check was stopped); early concrete prefix rewriting also hit kernel recursion.
The checked replacement proves view/header locality with an arbitrary size,
then instantiates that theorem. No budget was increased. The program and section header tables are now checked as well:
`Vsa/Sim/Boot/ElfEntries.lean` proves 56-byte/64-byte entry locality,
using the shared `parser_view_of_slice` and scalar-byte simplifier.
`gen_boot_elf.py` emits all four program and thirteen section records and
bounded entry certificates in `WhileMinElfTables.lean`; its two
`program_table_parse` / `section_table_parse` theorems compose the actual
source table parsers. The complete generated module checks in 4.5 s.
The complete parser and metadata increment landed as `efac856`, full gate passed:

* `Vsa/Sim/Boot/ElfSegments.lean` and `ElfSections.lean` prove actual
  segment/section/name-table interpretation as bounded views, sharing
  `Parser.mapM_ok`. NOBITS sections correctly require no file-backed extent.
* `WhileMinElfInterpret.lean` instantiates these summaries for all four
  segments and thirteen sections. `WhileMinElfFile.file_parse` constructs
  the actual `ELF64File`; `WhileMinElfMetadata.raw_file_parse` also proves
  the raw ELF class dispatcher accepts the exact archived full file.
* `gaps_geometry` proves the actual source gap calculation from its twenty
  metadata ranges. A generated `WhileMinElfSort` certificate uses quicksort's
  equations via `import all`, because its private well-founded recursion
  proofs prevent direct kernel reduction through the normal module interface.
  Only metadata is sorted; no byte array is materialized.
* `entry_metadata` and `tohost_metadata` establish the pinned Layout values;
  the latter checks the actual section-name search on the 112-byte table.

Direct full-file parser composition and concrete index elaboration hit the
existing recursion limit. Generic `elf64File_parse` / `rawElf64_view`
compose the parsers before specializing to the large view. The checked
replacement takes 0.8 s for the file proof and 1.2 s for metadata, with no
budget increase.

The concrete loader and closed reset-to-C-entry increment landed as `3535c09`,
full gate passed, in
`WhileMinElfLoaded.lean`: `loaded_memory` proves the actual source loader
builds `WhileMinImage.initialMem`, `whileMin_elf` supplies the complete
image/metadata contract, and `reset_caml_main_exists` gives the machine's
own reset and actual steps through crt0/main with no premises.
`LoaderViews.lean` shares geometry/byte correspondence and empty-piece
normalization for arbitrary ELF views. The generator emits the five source
loader descriptors (including the empty stack program header), pairwise
separation and symbolic byte aliases; no payload bytes are enumerated.
A direct concrete memory rewrite hit kernel recursion; `initializeMemory_views`
composes the abstract fold and removes empty ranges before instantiation.
The concrete loader/reset witness module checks in 0.8 s at default limits.

The first allocation-wrapper increment checks in `Startup/StatAlloc.lean`:
`statAlloc_dispatch` proves the generated nonpooling branch and tail jump
reach malloc, preserving memory/output and all general registers except a5.
`statAlloc_with_malloc` uses the existing `boundary_bind` rule to consume a
callee summary; it does not supply the allocator heap contract yet.
The generator emits the source blocks, call site and fixed-image projection.
New symbol pins (`pool`, stat allocator, malloc, domain initializer) come
from `gen_layout.py`, not handwritten data addresses.

`Startup/BssReads.lean` proves `clearWords_inside` / `clearWords_pins` by
induction over the abstract zeroing effect. `CrtCamlMainPost.pool_zero` and
`domain_zero` then derive the actual initial branch inputs through main's
two framed stores. The 12,549-word loop is never evaluated. A generic
`clearWords_log_pins` bridge keeps the full memory term opaque when supplying
these concrete facts. Both modules check in under two seconds.
Regenerating the required census also records the now-landed classifier
support (78,033 supported instructions); no ELF bytes changed.

Next: continue startup after `caml_main`, composing generated summaries
with the landed library and GC work. Reset-to-cut reachability and
the lane exit remain open.

The first startup increment landed as `917d0aa` after the full gate passed.
Checked startup progress (default proof budgets):

* `Startup.crt0_to_main` in `OCaml/Vm/Boot/Startup/ToMain.lean` proves
  execution from `_start` through the BSS loop and call to `main`, given
  the platform and code pins. Its post supplies `main`'s stack/link pins,
  global pointer, exact cleared memory, zero arguments and console frame.
* `Startup.clear_loop` uses `loopFromBody` with an indexed invariant and
  one generated guard/store/back-edge iteration. Its region and memory
  inputs are arbitrary, so it is reusable across embedded programs.
* `Startup.crt0_to_caml_main` in `Startup/ToCamlMain.lean` composes crt0
  with the complete `main` entry path and its call to `caml_main`. It
  supplies the exact two-write log, argv, stack and return link. The
  embedded header is preserved across BSS clearing (`clearWords_above`).
  `main_to_caml_main` is also reusable on its own with arbitrary argv/env.
* `gen_startup_rows.py` reuses `gen_fn.py`, `gen_sites.py` and the existing
  code-pin emitter. The call adapter retains named memory/register/output
  frames. Generator output is drift-checked; summaries are audited.
* BSS bounds, `_start`, global pointer and `environ` are extracted by the
  Layout generator. No data-address premise is a hand-written literal.

The main call-seam increment landed as `bb08069`, full gate passed.

Reset proof investigation: directly unfolding the complete `setupElf`
initializer exceeds the default recursion bound. `Vsa.Sim.FactorSail`
now factors closed bind syntax and emits a kernel-checked reflexivity
certificate; it does not execute Sail. The factored register initializer
supports `registers_metadata` and `setupElf_congr`, proving setup depends
only on entry PC and tohost metadata, without changing source or budgets.
`ElfReset` uses the runner's `initializeMemory` and `setupElf`, not the
captured register table. `ElfReset.pc` proves every successful reset ends
at the ELF entry. Loader correspondence and startup
callees remain open; existence/GoodState are now proved in `whileMin_reset_loaded_Statement`.

The reset metadata increment landed as `5768425`, full gate passed.

The register initializer and lookup foundations landed as `8e99cd2`, full gate passed.

Checked initialization progress:

* `initializeRegisters_program` and `initializeRegisters_run` in
  `Startup/InitializeRegisters.lean` cover the complete register initializer,
  for arbitrary input states and valid tohost metadata; its memory frame is
  `initializeRegisters_preserves_memory`.
* `NormalizeSail` reuses `Vsa.Meta.SimpNF` on the 101 factored fragments.
  `ReifyRegisterWrites` proposes typed assignment lists and checks program
  equalities; `RegisterWrites.run` supplies execution by one generic induction.
  All three layers retain kernel certificates and default proof budgets.
* Direct state-normal-form certificates elaborated but their final Lean checks
  remained unfinished after several minutes. They were stopped and are not
  claimed. The write-list abstraction checks the complete tail in about 1.2 s.
  The assignment list is proof-only (`noncomputable`); native compilation of
  this generated dependent list hit a Lean compiler IR error, while kernel
  checking the definition and its theorems succeeds.
* The primitive lookup region (16 instructions, six CFG blocks) and its
  strcmp call now have generated, checked rows. `gen_fn --region-end` validates
  bounds within the original function and keeps existing budgets. Invalid
  and oversized regions are rejected; the old startup output is unchanged.
* `Startup.strcmpSpecSign_zero_iff` in `CompareNames.lean` derives
  name equality from the landed strcmp sign spec and represented C strings.
  `strcmpSign_zero_iff` connects that observation to the zero-register branch.
  The counted inner lookup is now proved as described below.

The inner lookup increment landed as `a9f9eed`, full gate passed.

Checked inner builtin lookup:

* `lookup_run` in `Startup/LookupRun.lean` covers the real region
  `0x80024e0c` through `0x80024e4c`: initial name-pointer load, argument
  setup, JAL, arbitrary-length strcmp scan, final match and function-pointer
  load. It returns the resolved function in a1 and preserves memory/output
  and the caller register frame.
* `lookup_loop` in `Startup/LookupLoop.lean` uses `loopFromBody` and the
  measure `target - lookupIndex`. One symbolic `lookup_iteration` composes
  `lookup_head` with the generated index/load back edge. There is no concrete
  comparison replay or step-count-dependent kernel term.
* `NameTable` requires memory-only string/code/mask/window facts, a first
  matching index below 2^31, and nonnull pointer readbacks. These remain to
  be instantiated from the runtime image and loaded PRIM section; the outer
  403-entry construction/insertion loop is still open.
* `nextLookupIndex_nat` proves the signed ADDIW increment for every in-range
  index. `compare_names` converts the full aligned/unaligned library spec to
  the exact equality branch. All modules check under default proof budgets;
  `LookupLoop` takes about 2.8 s and `LookupRun` about 4.8 s.

The model/runner setup increment landed as `dd42be2`, full gate passed.

Checked model/runner setup:

* `model_init` in `Startup/ModelInit.lean` proves the actual Sail
  `sail_model_init` succeeds for arbitrary input states, preserves memory,
  output and cycle count, and supplies named reset CSR/PMA/signal pins.
* `LegalizeReset.lean` proves the three zero-valued CSR legalization calls
  with a readable misa. `InitializerFrame.lean` checks that the generated
  assignment list preserves nine seed registers. `RunnerDefaults.lean`
  certifies 21 initialized register values from the source-derived write list.
* `runner_setup` in `Startup/RunnerSetup.lean` composes model initialization
  with ELF-dependent register setup for any valid tohost metadata. The result
  has both `ModelSeed` and `RunnerDefaults`, plus memory/output/cycle frames.
  It checks in about 1.9 s; model initialization checks in about 7 s.
* `RegisterWrites.lastValue` / `registers_read` observe final register values
  without normalizing an accumulated machine state. The append/read and frame
  laws keep the complete initializer within default recursion limits.

Checked configuration and ISA-reset progress:

* `config_valid` (`Startup/ConfigValid.lean`) proves that the actual
  `config_is_valid` succeeds and preserves state when PMA regions are the
  model-initialized ones. Thirteen static checks, the three PMA regions,
  and both configured device windows have separate kernel certificates.
* `config_valid_program` reduces the outer check to `check_mem_layout`.
  `ConfigMemoryProgram` uses `#simp_nf` to normalize closed integer
  conversions before state composition. The PMA and outer checks now take
  about 0.7 s each. Earlier direct state-level compositions elaborated but
  consumed excessive memory during final checking; those runs were stopped
  and replaced by these completed program-equality proofs.
* `reset_misa_run` (`Startup/ResetMisa.lean`) proves the source `reset_misa`
  installs `initMisa` from the seed, preserves memory/output/cycles and
  frames every other register. This is one component of architectural reset.

All setup stages now have a composed execution proof and supply initial
GoodState. Initial executable-image facts and loader correspondence remain open.
Remaining startup functions include `caml_main`, GC
initialization, file/code loading, outer primitive-table construction, unmarshalling,
oldify/mopup and argv initialization. The first CFG inspection finds that
`caml_main` (482 instructions), `caml_init_gc` (160) and primitive-table
construction (160) exceed gen_fn's current whole-function budget. Their
summaries must compose smaller blocks/callees; the budget is unchanged.

## Round 1 status

Migration landed atomically as `7fa1750`, including the foreman's
`elf-fix` (`11989b1`) and all regenerated artifacts. Program files, argv and environment now live behind the fixed
three-pointer `.embed` header at `0x86800000`. One pinned runtime/Layout
serves every program. All five Sail runs passed. The closed theorem
`WhileMin.loaded_fillZero` now checks `Loaded` for the complete captured
while_min entry state. Its native provenance
is checked byte-for-byte, but reset-to-cut execution is not kernel-proved.

The closed witness landed via `scripts/integrate.sh` as `bc63ae6`. All
gate stages passed: 972 theorem audits with standard axioms, generator
drift checks, 39,600 pinned bytes with zero mismatches, the TCB quick
suite and abstraction gate. The lane exit is met for the captured cut.

## Image migration

* Pinned ELF rebuilt with `make -C c PROG=while.byte`; `make` now defaults
  to the committed `while.byte`. `c/ELF.sha256` pins the new 528,520-byte
  image: `b055163e2280efbec1d16c255afccf31e23315f9f37a7ffcba5bbed0850b1c99`.
* Census ran before layout generation. The decode table has 29,473 words
  in 231 chunks. The 1,459 allocator step lemmas remain covered. Library layout/pins,
  allocator steps/compositions, stdio and strcmp/string-copy specs, arm
  pilots and `OCaml/Vm/ImageData.lean` are regenerated by their generators.
* `.text`, `.rodata`, `.data` and `.tohost` match byte-for-byte across
  while, while_min, ocamlc-version, ocamlc-hello and ocamlc-hello-M1000.
  `scripts/check_boot_text.py` checks all four sections; the small-program
  and compiler-with-environment comparison pins are in `results/boot/`.
* The 31 early startup/HTIF function entries (including `_exit`, `_write`,
  `_sbrk` and `main`) move back four bytes; `caml_interprete` and newlib
  entries stay fixed. All regenerated addresses come from symbols.
* Mailbox migration uses `scripts/retarget_syi.py --mailbox-from` and is
  recorded in `results/retarget-mailbox.json`. `Vsa.Sim.tohostAddr` now
  references generated `LibraryLayout.tohostAddr`, with MMIO arithmetic
  proofs normalized through that layout rather than a stale literal.
* Allocator retargeting canonically matches `__heap_end`, which aliases
  `__embed_start`. The bin-header alignment theorem is generated from the
  actual ELF alignment (now 0 modulo 16), not the old image's 8.
* Main's primitive-summary generators, collector instruction fingerprints,
  collector/barrier segments and dispatch-table byte proofs are refreshed
  for the new image. Code-pin coverage is 39,056 bytes with no mismatch. Allocator address normalization unfolds
  the generated mailbox constant in both tactics and source templates.

## Validation

* Sail while: exit 0, expected output, 4,571,381 steps; cut 4,499,123.
* Sail while_min: exit 0, expected output, 4,312,978 steps; cut 4,269,257.
* Compiler version: exit 0, `4.14.4`, 54,416,092 steps; cut 48,827,370.
* Compiler hello-M1000: expected listing, exit 0, 77,438,363 steps; cut
  48,834,064. No collection after the cut.
* Compiler hello: expected listing, exit 0, 82,642,170 steps; cut 48,831,879.
  One minor collection and one major slice after the cut. All five Sail
  reruns are complete and recorded with ELF hashes in `c/results/`.
* Fresh while_min boot trace: 35,304 ordered stores; the same pinned layout
  is used. `young_ptr = 0x80281ce0`, `young_alloc_end = 0x80282000` (800
  allocated bytes); no pending work. The observation and generated small
  kernel checks are refreshed.
* Native candidate inspection places all 29 abstract heap objects and
  matches all 191 code words; this is preparation for the kernel witness.
* Core MMIO/load and allocator geometry builds passed after the layout
  changes. Full build, 790 headline axiom audits, generator checks, ELF
  and code pins all passed against the rebased main.
* TCB and host-mirror harnesses now implement the three-pointer header
  interface. The 329-trace quick suite has zero rejections on both Linux
  and the memory file system. Host-mirror while and compiler hello-M1000
  match the Sail outputs. `scripts/integrate.sh` landed the migration.

## Boot definitions and proofs

* `OCaml/Vm/Runtime.lean`: `RuntimeOk`, `runtimeLayout`, and
  `RuntimeOk.youngPtr_bounds`. Nonempty nursery allocations are ordinary
  heap blocks covered by `HeapRepr`. The free-list shape is a named
  parameter, not an arbitrary `True` instance.
* `OCaml/Refinement.lean`: `Loaded.platform` and `Loaded.runtime`; the cut
  must establish a running `GoodState`, intact executable image and runtime
  invariant. Dispatch-register initialization belongs to the prologue.
* `OCaml/Vm/Boot/WhileMinObservation.lean`: `bounds`, `noPending`, and
  `nursery_not_empty` are small, audited kernel facts about the observed
  projection. They do not certify machine reachability.
* `scripts/syi/gen_boot_witness.py ocaml-cut` streams stores and extracts
  the pre-step second interpreter entry. `scripts/gen_boot_observation.py`
  generates the scalar checks; check_all a5 checks drift.

## Closed captured-entry witness

`OCaml/Vm/Boot/WhileMin.lean` defines the concrete `cut` and proves
`loaded` and `loaded_fillZero` without hypotheses. The latter is
`Loaded (runtimeLayout BestFitSingleton) whileMin (fillZero cut)`.
All data comes from the machine capture, not a state constructed to fit
an abstract heap. This completes the lane's closed `Loaded` witness;
reset-to-cut reachability is a separate open execution theorem.

* `WhileMinImage.executable` proves the pinned text and read-only image
  survives the checked store log. Initial memory comes from the emulator's
  exact ELF initializer, including its auxiliary pieces.
* `WhileMinRegisters.good_state` proves the platform invariant from all
  176 defined registers. The full capture also supplies tick 1, step
  4,269,257, Sail cycle counter 1 and an empty console.
* `WhileMinPrimitives.bindings` proves all 403 PRIM-name/native-address
  bindings from the observed table, using the shared ELF-derived resolver.
* `WhileMin.control` discharges every remaining entry obligation. It
  composes with the existing heap, code, runtime and densification lemmas.
* Native `bootdump` independently ran `Vsa.setupElf` and 4,269,257 calls
  to `Vsa.stepOnce`. It checked all 560,326 mapped bytes and map cardinality
  against the complete loader-plus-store-log memory, then dumped every
  defined register and all counters/output. It took 115.75 seconds and
  124.9 MiB peak RSS. The hashes and capture are in `results/boot/`;
  reproduction commands are in `VALIDATION.md` §2.1.
* No native computation is a Lean proof assumption. Kernel theorems prove
  properties of the captured concrete state. The claim that this state
  was reached from reset has native validation, not a kernel run proof.
* The generators, capture helper, register/image/table certificates and
  axiom audit are included in the full gate. No proof-budget increases.

## Earlier landed certificates

The following sections record the incremental proofs. Their former open
control/image/memory premises are now discharged by the concrete witness
above; kernel startup reachability remains open.

## Checked store-log certificate

`WhileMinLog.logOk` and `WhileMinLog.memory_view` in
`OCaml/Vm/Boot/WhileMinLogChecks.lean` are kernel-checked for all 35,304
observed stores and 2,146 final runs (135,207 bytes). The build passed with
no heartbeat or recursion-budget overrides. These prove the exact memory
effect of the supplied store log for any initial memory. They do not prove
that Sail executed the log; `Loaded` is now supplied by the closed witness.

* `Vsa/Sim/Boot/Log.lean` ports the existing packed-log checker unchanged.
* `Boot/Checks.lean` composes small checks using `StoresChecked.join` and
  `RunTree.Checked.node`. `scripts/gen_boot_log.py` emits data and 128
  certificate parts, with at most 64 stores or bytes per kernel check.
* `Boot/Image.lean` ports the generic loader-memory lemmas.
* `Boot/Bytes.lean` projects total machine reads through a certified view.
* `OCaml/Vm/Boot/Heap.lean` gives finite closed-heap coverage through
  `HeapClosed.live_defined` and `HeapImage.repr`.
* `OCaml/Vm/Boot/FreeList.lean` defines the concrete startup singleton
  best-fit shape. Native inspection finds empty small lists and one blue
  large block, with self-linked list pointers, null tree children, and a
  size matching `caml_fl_cur_wsz`. Its memory-candidate proof now passes.
* `gen_layout.py` extracts best-fit structure sizes and offsets from
  `runtime/freelist.c` using the RV64 compiler, alongside ELF symbols.

The certificate is reproducible from the compressed observed log in
`results/boot/while_min-stores.jsonl.gz`; stage a5 checks generated drift.
Full Sail reachability remains open. The subsequent certificates instantiate
this byte view for the heap, code, runtime and complete captured cut.


## Concrete runtime certificate

The store-log certificate landed as `10ddb87`, with the full gate passing.
`WhileMinRuntime.fields`, `freeList`, `runtimeOk`, and `runtimeOk_fillZero`
now build: the collector invariant holds for a configuration whose memory
is zero-equivalent to the certified observed memory, including its
`fillZero` configuration. The free tree contains a blue block at
`0x80283008`, with 126,879 payload words and 126,880 total free words;
all sixteen small-list heads are null and their merge cursors point to
the respective head slots. These are proved from generated reads, not
assumed as observation fields. The complete capture now validates the
trace memory against Sail natively, and the closed `Loaded` theorem checks.

`observedMem_bytes_stored` removes the initial-memory dependency for reads
covered by stores. `bytesT_memEqv` reuses the model's zero-equivalence,
so the same read certificates cover densification. Runtime read generation
is drift-checked by stage a5. `boot_cut.py` now enumerates domain fields
from `domain_state.tbl`, excluding the newly added free-list offsets.


## Heap and entry-memory assembly

The runtime certificate landed as `5fd769b`, with the full gate passing.
The next checked piece establishes:

* `WhileMinHeap.objects`, `closed`, `separated`, `image`, and `repr`: all
  29 object layouts, string bytes/padding, reference closure, and pairwise
  non-overlap. The finite-image lemma supplies the production `HeapRepr`.
* `WhileMinEntry.code`: all 191 bytecode words at the observed code base.
  Entry reads also pin globals, `stack_high`, `extern_sp`, and `trapsp`.
* `WhileMinEntry.loaded` and `loaded_fillZero`: heap/code/runtime and entry
  memory assembled into `Loaded`, with the actual configuration's memory
  projection and `EntryControl` explicitly required. `EntryControl` carries
  PC, argument registers, empty console, `GoodState` and executable image.
  This is a conditional theorem, not the lane's closed exit witness.

The read emitter is shared in `scripts/boot_certificate.py`; heap and
entry generators are checked for drift. Object reads use the checked
store log only, with no invented heap contents or initial-memory premises.
The concrete cut-state control/image certificate and complete native
comparison now supply these premises.
