# Lane a6-gc

## F1 status (2026-10-05) — current

Done (F1 side of the GC):
- **`F1Pins.libHeap : LibHeap c`** (`OCaml/Vm/Gc/F1Heap.lean`). This is
  newlib's heap inside the F1 runtime invariant: a0-boot's `HeapReady H cap`
  with room 2^24. The runtime blocks `f1Extents` are covered (the
  `Caml_state` record, the remembered-set struct, `minorRegion`,
  `majorRegion`, the VM stack). So are the open channel records on
  `caml_all_opened_channels` (`OpenChannelList`), which lie apart from the
  extents and from each other.
  * `F1HeapSafe w` is the safe-window class and does not depend on `H`.
    `f1_stable`/`f1_window`/`f1_window_of` take it per window, and
    `f1_allocation` takes it per entry.
  * Instances: `heapSafe_domain`, `heapSafe_minor`, `heapSafe_major`,
    `heapSafe_stack`, `heapSafe_native`, `heapSafe_object` (placed objects
    via `NurseryGeometry.heapChunks`), `mutable_heapSafe`.
  * `f1_ignoredStatic` now covers `mutableStatics`, the ignored statics
    minus malloc's globals.
  * `NurseryGeometry` gained `heapChunks`, `nurseryLow` and `nurseryHigh`.
  * At the cut no channel is open (`libHeap_of`).
  * `whileMin_loaded_f1`, `whileMin_halts_f1` and `WhileMinOpen.libHeap` take
    a0-boot's named obligation
    `WhileMin.cut_heapReady_covers_Statement f1Extents`.
  * `f1_records`: writes to an open channel record (`OpenAt c a`, any
    `RecordWindow` missing the `next` link), alongside safe windows, keep
    `f1Runtime` (getD frame). It uses `LibHeapAt.keep_records`, and
    `OpenChannels.unique` makes the list determined by memory.
  * `F1Pins.gcIdle` (`f1_gcIdle`, a2-sem's `BarrierRuntime.idle`).
  * `Remembered.frameApart`/`aboveCode` are guarded by room.
  * `LibHeapAt.table : RefTableAt H chs c`: `Caml_state->ref_table` is
    the cut's struct, and the table is unallocated (as at the cut) or its
    storage is a live block apart from `f1Covered` and the open records
    (`RefStorage`). `f1Extents` (the writable class) excludes the table
    words, and a0-boot's obligation covers `f1Covered` (requested sizes).
    `F1Pins.codeWord`/`primsWord` pin `caml_start_code` and the prim
    table's contents to their blocks.
  * C-heap room: `LibHeapAt.room : reserved base #open ≤ cap`, which
    reserves `tableCharge = 2^19` while the remembered set is unallocated,
    plus `recordCharge = 2^17` per channel not yet opened, up to
    `maxChannels = 64` (`channelsBound`). The table's first growth spends its
    own reservation, so `f1_barrierGrowth` needs no room premise. A channel
    open spends one record and needs `#open < 64`, the per-program bound
    (foreman). `RefTableAt.minorWsz` pins `minor_heap_wsz = 2^18`, and
    `TableFree` keeps it and `ref_table` out of the writable domain windows.
  * `LibHeapAt.tableIn : (refTable, 56) ∈ H` (exact block, for `Grow.table`);
    a0-boot's obligation is `cut_heapReady_covers_Statement f1Covered
    [(refTable, 56)]`. `GrowDone.kept`: the growing barrier keeps every byte
    realloc keeps, except the slot. BarrierGrowth waits on a2-sem's
    `keep_field_step` and on the C-heap room decision (`LibHeapAt.room`
    is not kept by allocations; options are with the foreman).
  * `OCaml/Vm/Gc/F1Barrier.lean`: the parts of `BarrierRuntime f1Layout`.
    `f1_tableRuntime` gives `.table`: the remembered set as `Table`, its
    arena bounds, and `WindowSeparated` for the struct and the next entry,
    via `windowSeparated_of` (a window apart from `f1Uses` and the open
    records). `f1_insert` gives `.insert` (`LibHeapAt.insert`: both stores
    land in live blocks, the pointer stays in its storage). `.idle` is
    `f1_gcIdle`. `NurseryGeometry.codeFits`/`primsFit` bound P's code and
    primitives by the pinned blocks.
  * `Sim.f1_console_stable : ConsoleStable Gc.f1Layout`
    (`OCaml/Vm/Sim/F1Console.lean`), a1-prims' console premise. It covers
    the native window above the arena, the two errno words (mutable
    statics), and the record's offset/curr/buffer through `f1_records`,
    with the record open by `NurseryGeometry.channelsListed`.
  * LibraryReady's platform facts (F1-split row) cannot be runtimeOk
    fields. `WindowStable`/`MemoryStable` allow arbitrary registers in c',
    and `FrameOnD`/window frames do not keep byte presence. a1-arms carries
    `LoopRegisters.gp`/`htifIdle` and states C_CALL entries at `fillZero c`.
    a6-gc supplies `whileMin_gp`(`_fillZero`) and `fillZero_ram` (any c).
  * Next: `NurseryGeometry.channelsListed` (landed with a1-arms'
    channel-extent commit), `f1_console_stable` (a1-prims' `ConsoleStable`),
    the `refTable` pin, `BarrierRuntime f1Layout`, `BarrierGrowth f1Layout`
    (unallocated table, from `barrier_grow`).
- `F1Pins.console : ConsoleRuntime c` (a1-prims' console statics):
  `ConsoleRuntime.transfer` keeps it under any change to non-ignored static
  words; `consoleRuntime_of` reads it at the cut (file table, signals, lock
  words from `gen_boot_entry.py` reads; hooks and `_impure_ptr` from `.data`
  via `cut_imageWord`); `f1_consoleRuntime : ∀ c, f1Layout.runtimeOk c →
  ConsoleRuntime c`. `OpenChannels.lean`: the open-channel list
  (`OpenChannelList`, `OpenChannelsLinked`) for bprime's `open_descriptor`.
- `GcSafe` for programs without `Forward_tag` blocks:
  `OCaml/Bytecode/GcSafeNoForward.lean:gcSafe_of_noForward` (`NoForward P`:
  no reachable heap holds a tag-250 block; then every `FwdReduction` is the
  identity and `GcReach` collapses to `Reach`).
- `OCaml/Run/Checked.lean:checkAll_reach`: one kernel evaluation of a fold
  over a finite run proves a `Bool` predicate at every reachable state
  (`reach_of_checkAll` for BcSem). a2-sem can reuse it for `Good whileMin`
  (`ok s := step P s` is neither unsupported nor wrong).
- `OCaml/Programs/WhileMinShape.lean` (merged into a2-sem's single checked run `St.shapeOk`; no separate `decide +kernel`):
  `whileMin_fits : Fits g1Budget whileMin` (peak 18 stack / 125 heap words,
  100 initial), `whileMin_noForward`, `whileMin_gcSafe`.
- `OCaml/Vm/Gc/G1Room.lean`: `g1Budget = ⟨3584, 262044⟩` (two stack thresholds of slack) and the G1 room
  relation `G1Room B s c` (nursery `young_limit + 8*(B - words) ≤ young_ptr`;
  `stack_threshold + 8*B.stackWords ≤ stack_high`).
  `G1Room.nursery_capacity` gives `NurseryInput.capacity` in its exact shape;
  `G1Reserve.lean:NurseryReserve.of_room` gives a1-arms' `NurseryReserve`.
  `G1RoomDefs.lean` (below Refinement, for `Running`) holds `G1Room`/`g1Budget`;
  `G1RoomTransport.lean` holds `step`/`reserve`/`frame`/`same`. The stack
  field was dropped (a1-arms' `StackCapacity` + `RuntimeFrame` cover it).
  `G1Room.step` re-establishes it after a step (`G1Room.reserve`: directly from
  a `NurseryInput` reservation); `G1Room.stack_capacity` gives
  `EnterReady.capacity` from `StackRepr`.
- `OCaml/Vm/Gc/NurseryGeometry.lean`: the nursery counterpart of a1-arms'
  `StackGeometry`. `WindowSeparated w` proves `PayloadOutside`/`ImageOutside`/
  `BindingsOutside` once for any window; `NurseryGeometry` instantiates it
  with the free nursery `[young_limit, young_ptr)` and gives `NurseryInput`'s
  `headerWrite`/`youngWrite`/`limitRead`; `reserved_inside` puts the new
  block's writes in the window, `reserve_outside` + `OutWRange.shrink`
  re-establish it after the reservation. a1-arms: carry `NurseryGeometry`
  beside `StackGeometry` and `G1Room`.
- `OCaml/Vm/Gc/F1Runtime.lean` (requested by a1-arms): the pinned F1 layout
  `f1Layout := runtimeLayout F1Pins`. `F1Pins` fixes the cut's free block,
  `Caml_state` address, `stack_high` and `stack_threshold`; G1 keeps them.
  `f1_stable`: any window apart from `f1Footprint` (.bss, the young_*/stack
  domain fields, the free block) is `WindowStable`; corollaries
  `f1_domainField`/`f1_trapsp`/`f1_extern_sp`/`f1_local_roots`/
  `f1_exn_bucket`/`f1_external_raise`, `f1_nursery`, `f1_aboveBlock`,
  `f1_stackWindow`. `f1_stackHigh`/`f1_threshold`/`f1_quiet` give
  `RuntimeFrame`'s other fields. `f1_allocation`: `AllocationRuntime` for
  logs storing apart from the kept footprint and lowering `young_ptr` within
  the nursery. `whileMin_loaded_f1`(`_fillZero`): the cut is `Loaded f1Layout`.
  `NurseryGeometry.placement` gives a1-arms' `NurseryPlacement`;
  `NurseryGeometry.transport`/`frame_log` (non-allocating arms) and
  `NurseryGeometry.alloc` (after a reservation) re-establish the geometry,
  mirroring `StackGeometry`'s. Its heap field now covers every placed object.
  `WhileMinNursery.lean:whileMin_nurseryGeometry`: the geometry holds at the cut.
  Definitions moved low for the loop-head witness (a1-arms' `Running.stack`):
  `OCaml/Vm/RuntimeFields.lean` (`RuntimeFields`, `runtimeFields`) and
  `OCaml/Vm/Gc/NurseryDefs.lean` (`WindowSeparated`, `nurseryFree`,
  `NurseryGeometry`, `privateRegion`). New fields `heapDomain`, `heapPrivate`,
  `belowPrivate`: placed objects miss `Caml_state` and the private free block.
  `F1Runtime.lean:f1_objectField`: windows inside placed objects are
  `f1Runtime`-stable (SETFIELD/SETGLOBAL). Preservation lemmas live in
  `NurseryTransport.lean` (below `Sim/ReadOnly.lean`), with `NurseryGeometry.same`.
  `NurseryGeometry.alloc` now takes
  `capacity`.
  `f1Runtime`-stable (SETFIELD/SETGLOBAL). `NurseryGeometry.alloc` now takes
  `capacity`. `F1Pins.exit` (bprime): the exit path's four `.bss` globals,
  read by `f1_exitGlobals`; `gen_boot_entry.py` emits their cut reads.
  `F1Pins.trapBarrier`/`backtraceOff` (a1-arms, RAISE): `f1_trapBarrier`,
  `f1_backtrace`. `F1Pins.channelUnlock`/`f1_channelUnlock` (a2-sem). `f1_callbackDepth` (bprime, entry/STOP): the footprint's .bss
  window excludes `caml_callback_depth`. `f1_allocFrame_core` (a1-arms' `AllocFrame`):
  nursery reservations keep `f1Runtime`; `f1_allocFrame_core'` also allows
  VM-stack stores (CLOSUREREC). `NurseryGeometry.stackAbove`: young_ptr lies
  below the stack allocation. `stackWindow_apart`/`domainField_apart` let `Sim.F1Frame`
  avoid enumerating the footprint.
- `OCaml/Vm/Gc/G1Guards.lean`: the C fast paths' `young_ptr - bytes <u
  young_limit` guards. `double_room`, `small_room`, `string_room` give the
  `room` fields of `FastMemory`, `SmallAllocation.NurseryMemory` and
  `StringAllocation.NurseryGeometry` (a1-prims' allocating summaries) from
  `G1Room` plus the successor state's budget.
- `OCaml/Vm/Gc/WhileMinG1.lean:whileMin_g1Room`: room at the captured cut
  (`scripts/gen_boot_entry.py` now also emits `stack_low`/`stack_threshold`).

For other lanes:
- a1-arms: carry `G1Room B s c` in the common loop invariant. Each allocating
  family discharges `G1Room.step`'s `ptr` premise: `young_ptr` moves down by at
  most the words `BcSem` adds (header included); non-allocating arms leave
  `young_ptr`, `young_limit`, `stack_threshold`, `stack_high` unchanged.
- bprime: `whileMin_fits`, `whileMin_gcSafe` for the `Halts` instance; transport
  `whileMin_g1Room` from the cut to the loop head through the prologue.

## caml_modify (write barrier) for F1 — plan (2026-10-06)

a1-arms' SETGLOBAL/SETFIELD rows take `GlobalBarrier`/`FieldBarrier`/
`FieldBarrierK` (per-site `ModifyCallee`, `OCaml/Vm/Sim/ModifyCall.lean`);
a6-gc supplies them from one general summary. Measured at the pinned cut:
`caml_gc_phase = 3` (idle: `caml_darken` dead), `Caml_state->ref_table`
unallocated (base = ptr = limit = 0). whileMin runs exactly ONE barrier step
(SETGLOBAL, pc 188: a young block into the major global-data block), which
takes add_to_ref_table's slow path: `caml_realloc_ref_table` →
`realloc_generic_table.isra.0` → `caml_alloc_table` (35 instrs) →
`caml_stat_alloc_noexc` (21) → `malloc`/`_malloc_r` (569).
Paths (CFG of the 60-instruction body, rows in `Gc/Generated/Modify.lean`):
(1) young slot: store, ret; (2) major slot, old young: store, ret;
(3) old immediate/major (phase ≠ mark): value immediate/major: store, ret;
(4) value young, `ptr < limit`: store + entry + ptr bump; (5) as (4) with the
table full/unallocated: realloc call, then (4)'s insertion.
Plan: route modules for (1)–(5) in `scripts/gen_gc_rows.py` (segmentSummary
pattern, like `Immediate`/`BestFitSmall`); representation half from
`heap_field_written` + framing the ref-table stores; F1Pins gains `gcIdle` and
a remembered-set state field. Path (5) needs the library-heap invariant
(a0-boot's `RuntimeReady H capacity`, `stat_alloc_ready`) inside the F1
runtime invariant: the long pole for whileMin's `Halts`.

### caml_modify — composition design and library heap (2026-10-06)

- CFG (gen_fn): 18 blocks, 10 data-dependent branches (`a9a8`,`a9bc` slot
  young?; `a9cc` old immediate?; `a9ec`,`a9f8` old young?; `aa00` mark
  phase (dead: gcIdle); `aa0c`,`aa14`,`aa20` value young?; `aa28` table room?),
  returns at `a9c4`/`aa44`, calls at `aa50` (darken, dead) and `aa7c`
  (realloc). About 26 straight-line paths. Do NOT hand-write one route per
  path: build the missing abstraction first, a generated "branch-determined
  block DAG" summary (each branch's polarity a decidable predicate of the
  entry registers/loads; the summary is the disjunction of path posts,
  each path's ChainAccess composed from per-block access lemmas). Extend
  gen_fn/gen_gc_rows to emit the per-block access lemmas and the DAG fold.
- Library heap (a0-boot, 2026-10-06): `HeapReady H cap c` is memory-only and
  reads allocator globals and `vsaFoot H` (bytes outside live extents);
  `HeapReady.frame_live` frames windows inside live extents;
  `WhileMin.cut_heapReady_covers_Statement E` gives the cut fact covering
  chosen extents. F1 extents (payload address, request): Caml_state
  0x8007d150/928, ref_table struct 0x8007d500/56, nursery inside chunk
  0x80081730, major chunk 0x80282740 (free block + globals), VM stack
  0x803837b0/32768, code buffer 0x8038d7f0/764, prim table 0x8038fb10.
  Plan: `F1Pins.libHeap : ∃ H cap, extents covered ∧ HeapReady H cap c`;
  `f1_stable` additionally requires each window inside one F1 extent.
  a0-boot landed these as ec7fd92d. Integration is sequenced after the
  barrier's malloc path exists (it makes `whileMin_loaded_f1` conditional on
  the cut obligation and changes a1-arms' window lemmas).

### caml_modify slow route — progress and obstruction (2026-10-06)

- `OCaml/Vm/Gc/ModifySlow.lean`: the whileMin route's chain skeleton
  (a9a8T → a9ccT → aa0cF → aa14F → aa20F → aa28T → aa7c), `code_facts`
  (chain_facts over `Code.Caml_modifyLoaded`), `chain_ok`, the entry block's
  `slot_regs`/`slot_access`/`slot_control`, `old_regs` (frame as
  `sp + -32#64`, AllocEntry's `frameSp` idiom), and the memory helpers
  `stepMemM_of_addi`/`lpins8_stepMemM_sd` for a load after a store in one block.
- RESOLVED: the earlier "kernel deep recursion" came from stating the block's
  store addresses in a normalized shape. Stated in the evaluator's exact
  shape (`frame sp + BitVec.ofNat 64 24`, `fp + 0 + 0`) the logs and load/store
  addresses are `rfl`; a load after a store in one block goes through
  `stepMemM_of_addi`/`lpins8_stepMemM_sd`.
- `ModifySlow.prefix_run`: the actual machine route from `caml_modify`'s entry
  to its `jal caml_realloc_ref_table` (whileMin's barrier path), from a named
  `Route` of scalar observations (windows, pins, branch conditions);
  `ModifySlow.log`/`registers` give its exact store log and parked registers.
  Next: the realloc callee (caml_alloc_table → caml_stat_alloc_noexc → malloc,
  with a0-boot's HeapReady), the post-call insertion chain (aa88, aa38, aa44),
  and the represented ModifyReturn.

### caml_modify insertion chain and the realloc callee (2026-10-06)

- `OCaml/Vm/Gc/ModifyInsert.lean:run`: the actual blocks after
  `jal caml_realloc_ref_table` returns (aa88 reload table pointer/slot/ptr from
  the frame, aa38 `ptr := ptr + 8` and `*ptr := slot`, aa44 restore ra/sp and
  `ret`), from a named `Route`; `log`/`registers` give the exact effect. With
  `ModifySlow.prefix_run`, only the callee is missing for whileMin's route.
- The callee, on the unallocated-table path: `caml_realloc_ref_table`
  (8 instrs, tail-`j`) → `realloc_generic_table.isra.0` with `caml_alloc_table`
  INLINED: at `base == NULL` (0x80009750) it reads `Caml_state->minor_heap_wsz`
  (offset 80), stores `reserve = 256` and `size = wsz / 8` into the table,
  `__muldi3(size + 256, 8)`, `caml_stat_alloc_noexc` (a0-boot's
  `stat_alloc_ready` → malloc under `HeapReady`), then fills base/ptr/
  threshold/limit/end (more `__muldi3`, and `caml_gc_message` with
  `caml_verb_gc = 0`). Needed summaries at the pinned addresses: `__muldi3`
  (the Muldi3Spec battery, regenerated), `caml_gc_message` (quiet path),
  `caml_stat_alloc_noexc`.

- (2026-10-06) Large MAKEBLOCK/caml_alloc_shr/caml_initialize: the foreman
  moved wosize > Max_young_wosize out of F1 (InF1 + Fragment ledger); design
  recorded for F2 (ShrAllocated; no major slice under Fits g1Budget given
  caml_allocated_words ≈ 0 at the cut; lower heapWords to the free block or
  prove expand_heap; dynamic privateRegion via Split.placed).
- `scripts/gen_gc_rows.py` now also emits rows and code pins for
  `caml_realloc_ref_table` (ReallocRef), `realloc_generic_table.isra.0`
  (Realloc), the realloc callee's building blocks (`caml_gc_message` is
  a0-boot's `gc_message_quiet`; it is off the base == NULL path anyway).
- `scripts/gen_chain.py` (stage a5 `--check`) generates chain modules: for a
  straight route through generated rows it emits per-block registers (simp),
  logs (rfl), loads, access plans and controls, a named `Route`, `run`
  (`block_summary`), `log` and `registers`. Loads after same-block stores use
  `ChainGen.lpins8_stepMemM_keep`/`_apart`. It replaces hand-written
  ModifyInsert-style modules. The realloc callee's four chains are generated:
  `ReallocEntry` (a654 tail-j → 961cT → 9750, to the `__muldi3` call at 9774),
  `ReallocInstall` (977cF → 9784T → 9790, to 97a4), `ReallocLimit` (97a8, to
  97c0) and `ReallocReturn` (97c4, ret). Next: splice them with
  `call_summary` + `muldi3_summary` (×3) and `stat_alloc_ready` (HeapReady).
- **The realloc callee is proved** (`OCaml/Vm/Gc/ReallocCallee.lean:realloc_run`):
  `caml_realloc_ref_table` on an unallocated table (`base == NULL`), entry to
  `ret`, from `Entry` (a0-boot's `RuntimeReady H (capacity + charge)`, a
  `NativeFrame sp (64 + allocHeadroom)`, the table a live 56-byte block, its
  `base` word 0, `minor_heap_wsz`). `Done` names the fresh block `p`,
  `RuntimeReady ((p, request) :: H)`, the restored s0–s3/sp/ra and all seven
  table fields (base = ptr = p, threshold = limit = p + 8·size, end =
  p + 8·(size + 256), size = wsz/8, reserve = 256). Pieces:
  `ReallocPrefix.lean` (entry chain, `__muldi3`, `stat_alloc_ready`),
  `ReallocSuffix.lean` (install, limit, return, under `window_log`),
  `ReadyCalls.lean` (`ready_call`, `ready_muldi3`: any direct call / any
  `__muldi3` site under readiness), `Muldi3.lean:muldi3_registers` (the
  libgcc multiply as a `RegistersPost`, scratch registers present via
  `Muldi3Any.muldi3_spec_present`). `gen_chain.py` now also emits the `jal`
  `CallInstr` a chain parks at and the `ret` endpoint of a single-block chain.
  Open for whileMin's barrier: the memory frame of the callee (kept bytes for
  `f1Runtime`, via `ignoredStatics`) and the ModifySlow → callee →
  ModifyInsert splice with `Entry` from the F1 invariant (needs HeapReady in
  `F1Pins` and VsaOk at the interpreter state).
- `caml_modify` as generated segments (`gen_chain.py`, `Gc/Generated/Barrier*.lean`):
  slot class (`BarrierYoung` full young path; `BarrierAbove`/`BarrierBelow` to
  `a9cc`), old-value class (`BarrierOldImm`/`OldHigh`/`OldLow` to `aa0c`,
  `BarrierOldYoung` to `aa44`), value class (`BarrierValImm`/`ValHigh`/
  `ValLow` to `aa44`, `BarrierInsert` insertion to `aa44`, `BarrierFull` to
  the realloc `jal` at `aa84`), `BarrierReload` (after realloc) and
  `BarrierReturn`. Every path except the dead mark-phase branch. Next: the
  four-step memory-level composition (head, old, value, return), then the
  represented `ModifyCallee`. The generator now tracks the evaluator's exact
  in-block forms (`mv` leaves `x + 0`), supports `lw`, unsigned branches and
  `ret`/fall-through endpoints.
- `NurseryGeometry.channelsPrivate` (for a1-prims' `f1_flush_stable`): every
  placed channel record misses `privateRegion` (newlib's records lie outside
  the major heap's free block); kept by `transport`/`frame_log`/`alloc`/`put`,
  vacuous at the cut (no channel placed). Next: `F1Pins.libHeap` (decided with
  a1-arms: option A, the newlib heap inside f1Runtime; a0-boot generates the
  cut's chunk list `WhileMinHeapChunks`).
- **Machine caml_modify, growth path** (`OCaml/Vm/Gc/BarrierGrow.lean:barrier_grow`):
  with `Grow` (a0-boot's `RuntimeReady H (capacity + charge) sp ra` at the
  barrier entry, which carries VsaOk's full GPR presence; a native frame for
  the barrier, the callee and malloc; the remembered set unallocated; the slot
  in a live block apart from the table and `minor_heap_wsz`) and the path
  conditions (major slot, old not young, value young, `limit ≤ ptr`), the
  barrier runs `grow_to_call` (head, old class, `value_full`, readiness by
  `ready_step`, `ready_call`), `realloc_run` and `reload_run`, and returns with
  `GrowDone`: the fresh block `p`, `RuntimeReady ((p, request) :: H) capacity
  sp ra`, the callee-saved registers, the slot = v, `base = p`,
  `ptr = p + 8`, `*p = slot`. Every barrier step post now carries
  `present : GprPresent before → GprPresent after`; `realloc_run`'s `Done`
  gained `kept` (`Kept`: caller stack, low memory outside malloc's globals,
  live blocks but the table), `callee` (gp, tp, s4–s11) and `aligned`.
  This is whileMin's SETGLOBAL path. a2-sem is building the represented
  `ModifyCallee` on `barrier_fast`/`barrier_grow`.
- **Machine caml_modify, fast path** (`OCaml/Vm/Gc/BarrierRun.lean:barrier_fast`):
  from `Entry` (slot/value/ra/sp registers, `Caml_state`, young_start/end,
  the old value, `Phase_idle`, the frame and slot windows, separation from
  the read words and above-code stores) and `Remembered` (ref table words and
  windows), under `NoGrow` (young slot, or old young, or value not young, or
  `ptr < limit`), it returns to `ra` with `sp` restored and memory
  `writeLog entry log`, where `log` is `youngLog`, `majorLog` or
  `majorLog ++ insertLog` (`FastLog`), and every register outside
  x1/x2/x10–x15 is kept. Steps: `young_run`, `major_head`, `old_run` (four
  cases), `value_skip`/`value_insert`, `return_run`. Next: splice the growth
  path (`BarrierFull` → `realloc_run` → `BarrierReload`) with a named
  `GprPresent` premise (a0-boot: VsaOk's full presence is structural), then
  the represented `ModifyCallee` from `barrier_fast`.
- Barrier integration plan (after `realloc_run`). a1-arms' `ModifyCallee`
  (`OCaml/Vm/Sim/ModifyCall.lean`) is a represented summary from
  `ModifyInput` to `ModifyReturn` for every F1 program. Two invariant pieces
  are still missing before path (5) can run malloc from an interpreter state:
  (a) every GPR x1–x31 present (`VsaOk`; no loop invariant carries it yet;
  a0-boot's reset gives it at the cut, every arm's frame keeps it);
  (b) the library heap: `HeapReady H cap` with the F1 extents covered
  (a0-boot's `cut_heapReady_covers_Statement`). It reads malloc's globals,
  which `ignoredStatics` now excludes from `f1Runtime`. So the heap is a
  separate invariant component, kept by arms because they write only live
  blocks or non-malloc statics. Writes to `errno` (a1-prims) need a lemma
  that the room predicate ignores the errno words.
- Open domain question (records, not yet a blocker): for general F1
  programs the remembered set is unbounded. Alternating immediate/young
  writes to one major slot (only `SETGLOBAL` on global data reaches a major
  slot under G1) add an entry each time. At `threshold`, caml_modify requests a
  minor GC, which G1 excludes. whileMin inserts once. A bound needs a budget
  field (insertions ≤ wsz/8) or G2.
- `F1Runtime.ignoredStatics` (a1-prims request): `_impure_data._errno`,
  `oo_last_id`, `caml_callback_depth` and `errno` are carved out of
  `keptFootprint`; `f1_ignoredStatic : WindowStable f1Runtime ignoredStatics`.
  `in_bss` now takes `StaticApart x n` (decidable; `StaticApart.above` for
  ranges past `errno`). Follow-up: `ignoredStatics` now also covers every
  malloc global (`allocGlobal_ignored`), so `f1Runtime` survives malloc's
  static writes. `keptFootprint = staticKept ++ dynamicKept`, where
  `staticKept = gaps 0 ignoredStatics bss_end`. Consumers prove apartness with
  `footprint_apart` (static side: above `.bss` or inside one ignored word;
  then enumerate only the 7 windows of `youngWord :: dynamicKept`) or
  `footprint_apart_ignored`. Never enumerate `f1Footprint` directly.

Open: G2 (collector proper); status and next design step below. F1 asks from a1-arms/bprime are all landed (last: `72d88e40`).

G2 progress after F1:
- Fixed an unsatisfiable premise inherited from the WIP commit: the queued
  `CopyEffect` left its allocator log free, and `SourceFrame` quantified the
  effect and the publication independently, so any remaining source could be
  "overwritten" by a chosen log. `CopyChoice.lean:CopyStep` now ties the
  published table and the log to one branch (`Head.step_copy_step`;
  `step_copy_effect` is derived), and `CopyEffect.queued` keeps its
  `QueueAllocation`.
- `SourceOwnership.lean:OwnedFrame.sourceFrame` derives `SourceFrame` from
  `Nursery lo hi objects` (sources in the nursery, each with a field,
  footprints disjoint) and `OwnedFrame`: sources recorded, and root slot, copy
  target, queued payload, the two allocator effect logs and
  `oldify_todo_list` outside the nursery. `OwnedFrame.effect` proves every
  `CopyStep` branch's stores `Allowed`.
- Next: supply `OwnedFrame`'s address facts (targets/payloads from the major
  allocator's result range; allocator logs from free-list/frame windows) and
  `Nursery` from `HeapRepr` + `RuntimeOk` bounds.

Free-list placement (toward `OwnedFrame.targetOutside`/`payloadOutside`):
- `OCaml/Vm/Gc/FreePlacement.lean`: `BestFitSplit.Post.placed`: a split of a
  free block lying in `[lo, hi)` (`FreeIn`) returns a block in `[lo, hi)`
  ending where the source ended, and leaves the remnant `FreeIn lo result`.
  `freeIn_singleton`: the startup singleton block is `FreeIn` up to `heap_end`.
- `WhileMinG1.lean:whileMin_free_above_nursery`: the cut's free block starts
  above `young_end`, so splits from it never touch the nursery.
- `OCaml/Vm/Gc/SmallFreeList.lean`: `SmallChain lo hi size c a` (a
  null-terminated small list, every block in `[lo, hi)`), its frame law, and
  `SmallChain.pop` / `SmallListsIn.pop`: the actual exact-size pop returns a
  block in `[lo, hi)` and keeps all 16 lists in place.
- `OCaml/Vm/Gc/LargePlacement.lean:BestFitLarge.Split.placed`: the proved
  large path splits `bf_large_least`; if that block is `LeastIn lo hi`, the
  returned block lies in `[lo, hi)`, the least pointer is unchanged and the
  remnant stays `LeastIn lo result`. `whileMin_leastIn`: holds at the cut with
  `lo` above the nursery. (The tree-search/removal paths are not yet proved
  allocator paths, so no tree-wide invariant is needed by current proofs.)
  `FreeLists.small_result_placed`: the exact-size result header is placed by
  `SmallListsIn` alone (no effect analysis). `SmallListsIn.of_log`:
  route-independent preservation (static stores missing other slot heads,
  popped slot holding `next`), and `SmallListsIn.exact`: the actual
  `BestFitExact.effect` (plain, repair and empty routes) preserves it.
- Next (design): `OwnedFrame.targetOutside` needs the copying loop to know
  where `q.target` came from; `Head` records nothing about it. Targets come
  from the caller's first copy or from an earlier iteration's allocation
  (`QueueAllocation`/`IterationLog.exactSize|large`). Plan: (1) carry
  `SmallListsIn majorLo heapEnd ∧ LeastIn majorLo heapEnd` as the loop's
  `observe` (memory-only; preserved per branch by `SmallListsIn.exact` and
  `Split.placed`, other stores miss .bss and the free blocks); (2) add a
  `targetIn : q.target ∈ [majorLo, heapEnd)` field to `IndexedHead`,
  established by `small_result_placed`/`Split.placed` at each back edge and
  queued exit; (3) derive `targetOutside`/`payloadOutside` from
  `young_end ≤ majorLo` (`whileMin_free_above_nursery`/`whileMin_leastIn`).
  Refinement needed first: the allocator's own initializing stores land
  inside `[majorLo, heapEnd)` (in the block just popped), so `SmallChain.frame`
  (stores outside the region) is too strong. Strengthen the list invariant
  with pairwise-disjoint free blocks, and frame chains by "stores miss every
  remaining free block's first word" instead.
- Next: the
  general invariant over small lists and the large tree (every free
  block `FreeIn majorLo heap_end`), preserved by each `bf_allocate` path; then
  `OwnedFrame` target/payload facts from it.

## Source objects through the copying loop (2026-10-05)

- `CopyLoop.lean:run_copy_loop_indexed` generalizes the copying fold to views
  indexed by the growing forwarding table; `run_copy_loop_observed` is now its
  index-independent instance.
- `SourceObjects.lean:View.frame` keeps every still-unforwarded source object
  through a disjoint store log (Eqv object frame); `View.initial` starts from
  any represented nursery (no empty-nursery premise).
- `CopySources.lean:run_copy_from_head_sources` runs the real loop retaining
  all remaining source objects. `SourceFrame` (finite footprint ownership)
  stays an explicit premise.

## Completed ancestor objects and terminal fields (2026-10-04)

- `WordFamily.lean:wordFamily_frame` shares Eqv framing for finite scalar
  predicate families; completed roots and copied headers both instantiate it.
- `CopiedHeaders.lean:ancestor` combines a retained typed header, a genuinely
  rewritten ancestor field, and the final child table entry into the complete
  singleton ObjAt at the final placement. It does not require an acyclic heap.
- `SingleFieldPayload.lean` proves fixed/non-pointer terminal fields at
  the loop-body interface. Forwarded and whole-call field proofs now share
  `single_field_relocated`; source capture shares `child_original`.
- Targeted build/regressions pass (783 jobs), full Audit passes (3700 jobs),
  and both discipline gates pass; only permitted axioms. Tail-header
  checkpoint landed as `429d50f`.
- Next: carry these evolving header/field observations through the loop,
  preserve original unforwarded payloads, and derive ownership coverage.
  Remaining routes, full collector closure, G2 and live budget remain open.

## Typed headers for tail allocations (2026-10-04)

- `FreshHeaderCore.lean:header_of_typed_wrapper` shares the real wrapper
  header proof across native entry and tail entry; header color may differ
  while size/tag agree. Shared address laws exclude modular wraparound.
- `ContextHeader.lean` proves typed headers for both tail allocator routes,
  natural header addresses from actual RAM windows, and preservation by
  queue insertion.
- `SingleFieldChildHeader.lean` connects these facts to actual captured-child
  allocation results, retaining the preceding parent-forwarding log.
  Counter/header separation remains a finite ownership premise.
- Targeted/header regressions pass (766 jobs), full Audit passes (3697 jobs),
  and both discipline gates pass; only permitted axioms. Wide caller-root
  checkpoint landed as `d89dc58`.
- Next: retain typed copied headers and completed/pending fields across the
  loop, derive ownership coverage, then cover the remaining collector.
  G2 and live budget remain open.

## Roots through scalar and queued exits (2026-10-04)

- `CopyChoice.lean:Head.step_copy_effect` exposes exact parent-prefix plus
  suffix logs for both scalar and queued exits.
- `CopyLoop.lean:run_copy_loop_observed` retains memory observations using
  pure concrete-log frame laws; the table-only API delegates with True.
- `CopyRoots.lean:run_copy_from_head_root` publishes the initial caller root
  and preserves it through both exit kinds. Its result uses the existing
  `RootReturned.represented` typed final-table interpretation. The existing
  scalar-only root theorem keeps its original footprint premises.
- `CopyRootFrame` and initial-root footprints remain explicit ownership
  suppliers. Full object/queue representation is not yet the loop invariant.
- Targeted build passes (767 jobs), full Audit passes (3692 jobs), and
  both discipline gates pass; only permitted axioms. Wider loop landed
  as `877f28e`.
- Next: typed tail-allocation headers and completed/pending payloads, then
  ownership coverage and remaining collector routes. G2/live budget open.

## Copying loop with queued-child exits (2026-10-04)

- `CopyChoice.lean` adds actual fresh multi-field child exits to the
  ordinary branch set. `QueueAllocation.run` selects either proved allocator
  from data; `Head.step_copy` records exact one- or two-copy publications
  and strict progress. No execution premise is introduced.
- `CopyLoop.lean:run_copy_from_head` folds real back edges and scalar or
  queued exits, retaining complete/bounded partial tables and the initial
  native return. Existing ordinary Coverage embeds via `Coverage.toCopy`.
- `CopyCoverage` remains an open reachable-head data/ownership obligation.
  Final table/native restoration is proved; full typed heap and work-queue
  invariants are not yet carried by this loop.
- Targeted build passes (764 jobs), full Audit passes (3665 jobs), and
  both discipline gates pass; only permitted axioms. Two-publication
  invariant landed as `0a27b6a`.
- Next: retain root/pending/completed payload views through wider coverage
  and derive ownership suppliers. Other tags/allocator paths, full collector
  closure, G2 and live budget remain open.

## Two-publication queue exit invariant (2026-10-04)

- `QueuedChildTable.lean:QueuedChild.table` retains both the parent and
  queued child in the real partial table. `QueuedChild.complete` preserves
  zero-header coverage from exact finite store footprints.
- `ForwardingTable.Complete.progress` proves strict copying progress when
  old table entries survive and at least one fresh source becomes forwarded;
  an iteration may publish several objects. `extend_many` shares coverage
  reasoning for these batches.
- `SingleTailQueued.lean:Head.finish_queued` restores the initial native bank
  and returns the complete two-entry extension plus strict progress. The
  concrete QueuedChild result retains intrusive queue/pending payload facts.
- `LoopFold.lean:loop_to_exit` factors PC-guarded iteration via the machine
  loop kernel; the ordinary observed loop reuses it with unchanged APIs.
- Targeted build passes (764 jobs), full Audit passes (3658 jobs), and
  both discipline gates pass; only permitted axioms. Queue machine
  checkpoint landed as `c7fc21f`.
- Next: incorporate queued exits into the loop branch coverage, retain
  typed ancestor/pending fields, and derive ownership suppliers. Other
  collector routes, closure, G2 and live budget remain open.

## Fresh multi-field child queue continuation (2026-10-04)

- `ContextQueue.lean:ContextAllocated.enqueue` executes the actual queue
  insertion and native return on an existing oldify frame, preserving the
  earlier saved bank through explicit store footprints. `enqueue_after`
  shares allocation/queue composition.
- `SingleFieldQueuedChild.lean:prepare_enqueue_child` and its large variant
  compose real parent forwarding, either proved allocator, child insertion,
  and native return. These cover a fresh multi-field child rather than a
  size-one back edge. The queue conditions enforce size greater than one.
- `ContextQueued.payload` retains the typed pending payload for mopup using
  shared `pendingPayload_of_writeLog`; first-entry queue results reuse it.
- Targeted build/regressions pass (774 jobs), full Audit passes (3615 jobs),
  and both discipline gates pass; only permitted axioms. Caller-root
  checkpoint landed as `6de5244`.
- Next: retain both newly published table entries and incorporate queued
  exits into collector composition. Ownership suppliers, all ancestor
  payloads, other tags/routes, G2 and live budget remain open.

## Caller root through the ordinary tail loop (2026-10-04)

- `SettledRoots.lean` expresses completed roots/ancestor fields as Eqv
  observations, proves publication by the actual first prefix store and
  framing through disjoint logs, and recovers their typed meaning from the
  final forwarding table. Both allocation back edges and exits instantiate it.
- `SingleTail.Head.step_effect` exposes the four concrete store alternatives.
  The shared `run_loop_observed` folds these effects with a proved memory
  frame; previous tracked/untracked APIs retain their original contracts.
- `SingleTailRoots.lean:run_from_head_root` publishes and retains the initial
  caller root through the real loop and return; `RootReturned.represented`
  gives its typed value under the final table. `RootFrame` and initial root
  footprints are explicit data-only ownership obligations, still open.
- Targeted build passes (757 jobs), full Audit passes (3609 jobs), and
  both discipline gates pass; only permitted axioms. Fixed terminal fields
  landed as `2bd72dc`.
- Next: connect all completed ancestor fields and pending payloads, derive
  ownership coverage, and cover remaining object/allocator paths. G2,
  collector closure, and live budget remain open.

## Fixed terminal fields at the final placement (2026-10-04)

- `FreshSingleFixed.lean:SingleResult.payload_fixed` transports the original
  field through the actual whole-call result using `Eqv.transport`.
  `payload_nonpointer` and `payload_outside` discharge the typed action
  for non-pointers and old base pointers outside the finite source set.
- `SingleObject.lean:single_object_of_payload` assembles the typed singleton
  from its header and field; both forwarded and fixed terminal proofs use it.
  `SingleResult.object_fixed` accepts the header proved by either allocator.
- Targeted build passes (760 jobs); full Audit passes (3598 jobs), with
  only permitted axioms. Both discipline gates pass. Domain checkpoint
  landed as `2cc48df`.
- Next: preserve caller roots and completed ancestor fields across the
  loop. Full ownership coverage, other routes, G2 and live budget remain open.

## Tail-loop partial-map domain (2026-10-04)

- `ForwardingDomain.lean:domain_iff` characterizes the table domain as
  exactly the zero-header sources in the finite original source set, under
  Bounded and Complete. Outside addresses stay fixed; `nonYoung_fixed`
  supplies the typed base-pointer action from actual nursery rejection.
- `SingleTail.run_loop_tracked` is the shared machine fold for list properties
  preserved by actual one-parent publication. `run_from_head_bounded`
  retains the source-set bound through the real loop. Existing untracked
  interfaces retain their original premises and guarantees.
- Targeted build passes (755 jobs), and full Audit passes (3581 jobs)
  with only permitted axioms. Both discipline gates pass. Ordinary
  loop checkpoint landed as `468074f`.
- Next: connect fixed-value exits to the final placement, retain caller
  roots and typed pending/completed payloads, and derive data Coverage
  from ownership. Other collector routes, full G2 and live budget open.

## Ordinary single-field tail loop (2026-10-04)

- `SingleTailLoop.lean:run_loop`/`run_from_head` fold the actual back edges
  and immediate/non-young/forwarded exits with `loopFromBody`. They return
  through the initial saved link/bank, preserving output and native frames.
- `Coverage` is an explicit **open data-only premise** on reachable heads:
  it supplies concrete branch/header/allocator observations and footprints,
  plus a distinct native return site. No callee or whole-loop execution is
  assumed. This is an ordinary single-field subloop, not G2 completion.
- `ForwardingComplete.lean` strengthens the invariant: every zero-header
  source in the finite source list has a published entry. The returned
  table supplies the typed action for each such base pointer.
- Targeted build passes (754 jobs), as does full Audit (3566 jobs), with
  only permitted axioms. Both discipline gates pass. Concrete
  back-edge checkpoint landed as `341760d`.
- Next: retain typed pending/finished payloads and caller roots across the
  loop, and derive Coverage from heap/free-list ownership. Other object and
  allocator paths, roots/mopup/ephemerons, collector closure, G2 and live
  budget remain open.

## Concrete fresh single-field back edges (2026-10-04)

- `SingleFieldBackEdge.lean:backedge_exact` and `backedge_large` prove
  the actual next forwarding boundary and its full register/RAM interface,
  partial-table extension, original source membership/freshness, native-bank
  preservation and strict copying-rank decrease.
- `TailProgress.forwarding_then_decreases` frames the rank through the
  child allocator; `BackEdgeConditions` names finite ownership footprints
  and next write windows, without assuming execution or a post-invariant.
- `StoreReturn.as_oldify` shares both decoded epilogues at the saved-word
  interface; original-caller restoration now delegates to it.
- Targeted build and whole-call/header regressions pass (768 jobs). Full
  Audit passes (3533 jobs), with permitted axioms; both discipline gates
  pass. Forwarding-table checkpoint landed as `a2f896f`.
- Next: construct the ordinary single-field loop invariant and combine
  concrete back edges with immediate/non-young/forwarded exits using the
  machine loop rule. Typed pending payloads, ownership suppliers, other
  routes, full collector closure, G2 and live budget remain open.

## Published forwarding component of partial relocation (2026-10-04)

- `ForwardingTable.lean` expresses published entries with Eqv combinators.
  `publish_then` derives extension through the real prefix plus separated
  allocation log; `extends_published` proves the sparse map keeps all
  previously published source mappings when the new source is fresh.
- Functionality follows from the concrete source word. `pointer_action`
  turns the table into the typed base-pointer relocation observation.
- `SingleFieldTable.lean` connects both child allocation results to table
  extension. `ForwardedReturned.payload_from_table` derives its typed
  result without a separate scalar forwarding-action premise.
- Targeted builds pass (747 jobs); full Audit passes (3521 jobs), with
  only permitted axioms. Discipline and
  abstraction gates pass. Child/rank checkpoint landed as `eb0498a`.
- This is the forwarding component, not the whole invariant: target
  injectivity/freshness, pending payloads, native-bank preservation and
  complete loop composition remain to be assembled. G2/live budget open.

## Captured fresh-child allocation and copying-step rank (2026-10-04)

- `SingleFieldFresh.lean:prepare_allocate_child` and
  `SingleFieldFreshLarge.lean:prepare_allocate_child_large` prove parent
  forwarding, actual child classification and either complete child
  allocation on the existing frame, retaining the exact combined write log.
- `ContextLargeAllocated.lean:allocate_context_large` adds the complete
  least-large-block tail allocation alternative. Both child paths share
  header/input and log/frame composition.
- `TailProgress.lean:YoungHead.decreases` proves the finite nonzero-source-
  header count strictly drops under the actual forwarding prefix and other-
  header separation. It is the copying-step rank component: Forward-tag
  shortcuts and mopup need additional control/pending-field progress.
- The law check covers 528 rank-decreasing prefixes, alongside all earlier
  cyclic/aliased/special-tag cases. Targeted build passes (741 jobs).
  Full Audit passes (3514 jobs), with permitted axioms; discipline and
  abstraction gates pass. Context checkpoint landed as `a390302`.
- Next: assemble the ordinary single-field tail invariant and its machine
  loop, tying allocation freshness and header separation to heap ownership.
  Other object/allocator routes, global collector closure, G2 and the live
  budget remain open.

## Fresh-child tail allocation context (2026-10-04)

- `AllocationContext.lean:prepare_context` starts at the fresh header
  classifier and executes the real allocation JAL on the existing frame.
  `AllocationContext.finish` shares return pins, constants and code
  preservation with the original `AllocationEntry.finish`.
- `ContextAllocated.lean:allocate_context` executes the complete exact-size
  allocator from this tail entry, with concrete initial-memory free-list
  conditions and an allocator-only write log. No native prologue is replayed.
- Targeted context build passes (695 jobs), as do prior whole-call
  regressions after the shared-frame refactor (759 jobs). Full Audit
  passes (3503 jobs), with permitted axioms; discipline/abstraction gates pass.
  Whole forwarded-child checkpoint landed as `bf52360`.
- Next: connect captured young-child heads to this context, add the large
  allocation alternative, and express fresh-child progress in the partial
  relocation invariant. Ownership/collector closure, G2 and live budget open.

## Whole fresh-single forwarded-child calls (2026-10-04)

- `FreshSingleForwarded.lean:single_fresh_forwarded` and
  `single_fresh_large_forwarded` compose real oldify entry, either allocator,
  forwarded young-child tail processing and original caller return.
- `ForwardedSingleResult.payload` and `FreshSingleForwardedHeader.lean:object`
  establish the represented object at the relocated placement from the
  original object, allocator header, forwarding word and explicit footprints.
- `AllocationResult.single_prefix_input` now shares the size/prefix adapter
  across all child routes; existing immediate/non-young/header regressions pass.
- Targeted builds pass (757 jobs plus header target); full Audit passes
  (3492 jobs), with permitted axioms. Discipline and abstraction gates pass.
  Forwarded-child/self-cycle checkpoint landed as `d28c873`.
- Next: factor an allocation-call context independent of native entry, so
  fresh children can allocate on the existing tail frame. Then extend the
  partial-relocation invariant. General ownership/collector closure, G2 and
  live-word budget remain open.

## Forwarded young child and self-cycle return (2026-10-04)

- `SingleFieldForwardedReturn.lean:return_young_forwarded` composes the
  actual parent forwarding, child tag/range tests, zero-header child route
  and native epilogue. `ForwardedReturned.payload` gives the typed relocated
  child via Eqv, with a named forwarding-table observation.
- `ForwardingPrefix.lean:forwarding_prefix` derives a common raw forwarding
  view from the real three-store log. `SingleFieldSelf.lean:return_self`
  uses it to execute a single-field self-cycle: the final field equals the
  copy address, with no assumed zero-header/forwarding-pointer contents.
- Targeted Lean builds (670 jobs), full Audit (3490 jobs) and both proof
  discipline gates pass; new headlines use only permitted axioms.
  Young-child entry checkpoint landed as `a218e3e`.
- Next: compose this return with both allocations and the original caller,
  then extend the partial relocation to fresh children. Ownership suppliers,
  remaining object/allocator routes, collector closure, G2 and live budget
  remain open.

## Fresh single-field young-child tail entry (2026-10-04)

- `SingleFieldYoung.lean:prepare_young` proves the actual forwarding, child
  tag and accepted nursery-test path to the header classifier. It retains
  the captured original child, destination, native frame and prologue constants.
- `FreshSingleYoung.lean:single_fresh_young` and `single_fresh_large_young`
  compose both allocation alternatives to this tail boundary; `captured`
  gives its original-placement `Eqv.valRead` interpretation. No initialized
  destination payload or recursive execution is assumed.
- `SingleFieldForwarded.lean:YoungHead.forwarded_return` connects this
  boundary to the existing actual zero-header path and native return.
- The law check now covers captured self-pointers: the source is already
  forwarded while the register still contains its old address. All law
  checks pass; targeted Lean builds and full Audit (3487 jobs) pass,
  with only permitted axioms. Discipline and abstraction gates pass.
- Previous whole non-young checkpoint landed as `43372a6`. Next: compose
  the young forwarded-child return with the original saved bank and typed
  relocated payload, then extend the partial relocation for fresh children.
  Collector closure, ownership suppliers, G2 and live-word budget remain open.

## Whole fresh-single non-young routes (2026-10-04)

- `FreshSingleNonYoung.lean:single_fresh_nonYoung` and
  `single_fresh_large_nonYoung` prove actual oldify entry through either
  allocator, even-child nursery rejection, final field store and original
  caller return. They reuse `SingleResult` payload and typed-header proofs.
- `AllocationResult` now retains the actual prologue loop constants,
  including the runtime-domain and tag registers. They are derived from
  machine frames; no new caller-supplied register premise was introduced.
  `single_input`, `single_geometry` and `complete_single` share entry and
  result composition with immediate children.
- Targeted builds and all fresh-single/header regressions pass (749 jobs);
  discipline and abstraction gates pass. Full Audit passes (3440 jobs),
  with only permitted axioms. Even-child continuation landed as `f98bb22`.
- Next: young-child tail entry and its partial relocation invariant.
  Other object/allocator routes, ownership suppliers, collector closure,
  G2 and the ocamlc live-word budget remain open.

## Single-field even non-young continuation (2026-10-04)

- `OldifyYoung.nonYoung_machine` proves both actual nursery-rejection
  edges using the accepted path's scalar load certificates.
  `SingleField.return_even_nonYoung` composes forwarding, child tag test,
  strict range rejection, final field store and original saved-bank return.
- `ReturnReady.finish` shares restoration across immediate and non-young
  children. `ReadInput` separates nursery observations from accepted-range
  bounds; existing young and immediate routes retain their statements.
- Targeted builds and complete fresh-single/header regressions pass
  (748 jobs); discipline and abstraction gates pass. Full Audit passes
  (3419 jobs), with only permitted axioms. Whole fresh-single immediate routes landed as
  `41dfc6b`.
- Next: retain the derived runtime-domain register in allocation results
  and compose whole fresh non-young single-field calls. Young-child tail
  composition, other object/allocator routes, ownership suppliers,
  collector closure, G2 and the ocamlc live-word budget remain open.

## Whole fresh-single immediate routes (2026-10-04)

- `FreshSingle.lean:single_fresh` and `single_fresh_large` prove actual
  oldify entry, either proved allocation alternative, single-field
  forwarding, immediate-child store and original caller return.
  `AllocationResult.single_immediate` shares the entire continuation.
- `NativeRestore.lean` identifies both restore orders with the original
  caller through a generic register-list permutation lemma.
  `FreshSingleData.lean:SingleResult.payload` proves the represented
  single-field payload, using explicit allocation/root separation.
- `FreshSingleHeader.lean:single_exact_header`/`single_large_header`
  retain source size/tag in mopup's natural-address interface. The shared
  `header_of_suffix` also supplies queue header preservation.
- Targeted builds and queue/header regressions pass (745 jobs); discipline
  and abstraction gates pass. Full Audit passes (3378 jobs), with only
  permitted axioms.
  Immediate single-field continuation landed as `ea450b0`.
- Next: even-child nursery classification and non-young return, then young
  child tail-loop composition. Other object/allocator routes, ownership
  suppliers, collector closure, G2 and the ocamlc live-word budget remain open.

## Complete single-field immediate-child continuation (2026-10-04)

- `SingleFieldReturn.lean:return_immediate` proves forwarding, actual
  child classification, final field store and native return. Its exact
  effect has four stores, and its return PC and saved registers refer to
  memory before forwarding. `StoreReturn.restored_of_savedSame` shares the
  existing oldify saved-bank observation interface across both epilogues.
- `ReturnConditions.of_memory` transports the pure geometry, branch and
  saved-return observations to an actual allocation result.
- Targeted build passes (626 jobs); discipline and abstraction gates pass.
  Full Audit passes (3370 jobs), with only permitted axioms. Store/return landed as
  `3685356`.
- Next: whole fresh-oldify composition for immediate single-field children
  across both allocator alternatives. Even-child nursery continuation,
  other object/allocator routes, ownership suppliers, collector closure,
  G2 and the ocamlc live-word budget remain open.

## Oldify destination store and native return (2026-10-04)

- `StoreReturn.finish` proves the actual restore/store/return path reached
  by immediate single-field children. It retains the destination value,
  exact singleton write log, restored native registers and return PC.
- `Generated/StoreReturn.lean` derives both restore blocks, slot offsets
  and stack adjustment from the ELF. Access uses total reads; explicit
  destination/stack separation protects the three loads after the store.
- Targeted build passes (601 jobs); discipline and abstraction gates pass.
  Full Audit passes (3359 jobs), with only permitted axioms. Child classification landed
  as `33e020e`.
- Next: compose this return with single-field forwarding/classification
  and the fresh allocator routes. Even-child nursery continuation, other
  object/allocator routes, ownership suppliers, collector closure, G2 and
  the ocamlc live-word budget remain open.

## Both single-field child tag branches (2026-10-04)

- `ChildClassify.classify` executes both actual child-tag branches and
  the immediate branch's jump. `SingleField.prepare_classify` composes
  forwarding and classification, retaining the captured child, new
  destination, exact three-store log, code and native frame.
- Generated branch selection is determined by the child word. Even
  children reach nursery-range tests; odd children reach the native
  store/return continuation. No child-run premise is assumed.
- Targeted build passes (621 jobs); discipline and abstraction gates pass.
  Full Audit passes (3350 jobs), with only permitted axioms. Single-field prefix landed
  as `6e7be63`.
- Next: store/return for immediate children, then even-child nursery
  continuation and composition with the fresh allocator routes. Other
  object/allocator routes, ownership suppliers, collector closure, G2 and
  the ocamlc live-word budget remain open.

## Single-field forwarding prefix (2026-10-04)

- `SingleField.prepare` proves the actual size-one branch after root
  update, source-header zeroing and source forwarding-pointer store,
  reaching the child tagged-value test. Its post retains the captured
  child value, exact prefix log, code and machine frame.
- `scripts/gen_gc_rows.py` emits `Generated/SingleField.lean` from the
  pinned ELF. It reuses the queue prefix body certificates.
  `WorkQueue.PrefixWindows` factors the three required write windows
  from the queue-only target-field windows.
- Targeted build passes (618 jobs), with exact-size/large queue regressions
  also checked; discipline and abstraction gates pass. Full Audit passes
  (3347 jobs), with only permitted axioms. Large-route typed headers landed as
  `7c2457a`.
- Next: child tagged-value classification and tail continuation for the
  single-field route. Other object/allocator routes, ownership suppliers,
  collector closure, G2 and the ocamlc live-word budget remain open.

## Typed headers after the large-block fresh route (2026-10-04)

- `FreshLargeHeader.lean:LargeEnqueued.header` proves original size/tag
  agreement after large allocation and queue insertion. `header_nat`
  provides mopup's natural-address interface; `header_address` derives
  nonwrapping payload arithmetic from the actual header write window.
- `AllocWrapperCore.header_of_effect`, `header_of_wrapper_effect` and
  `QueueResult.header` share saved-tag readback, source-header facts and
  queue preservation across both allocation alternatives. Existing
  exact-size header proofs now instantiate these helpers.
- Targeted builds and exact-size regression pass (733 jobs); discipline
  and abstraction gates pass. Full Audit passes (3344 jobs), with only
  permitted axioms.
  Complete large queue route landed as `62324e5`.
- Next: single-field fresh scanned-object tail route. Other object and
  allocator routes, ownership suppliers, collector closure, G2 and the
  ocamlc live-word budget remain open.

## Fresh large-block queue route and native return (2026-10-04)

- `FreshLargeEnqueued.lean:enqueue_fresh_large` proves complete actual
  fresh oldify through least-large-block allocation, forwarding/root/queue
  stores and original caller return. `QueueResult.payload` provides the
  represented grey payload through the relocation Eqv interface.
- `AllocationResult.enqueue`/`saved` share queue continuation and native
  save-bank readback across both allocator alternatives. The exact-size
  route and payload proof now instantiate this common interface.
- Targeted large-route/FreshHeader regression passes (731 jobs); discipline
  and abstraction gates pass. Full Audit passes (3340 jobs), with only
  permitted axioms.
  Fresh large allocation landed as `0903f7c`.
- Next: shared original-size/tag header readback and large-route natural
  header address. Other allocator/object routes, ownership suppliers,
  collector closure, G2 and the ocamlc live-word budget remain open.

## Fresh oldify through large-block allocation (2026-10-04)

- `FreshLargeAllocated.lean:allocate_fresh_large` proves actual oldify
  entry through the least-large-block wrapper route to queue entry.
  `AllocationEntry.finish` shares exact memory composition and native
  register preservation across this and the existing exact-size route.
- `Prepared.image` shares code transport through oldify saves.
  `AllocFinish.effect_high` shares continuation footprints; the complete
  large-route footprint now requires only pure memory-window conditions.
- Targeted builds and FreshHeader regression pass (729 jobs); discipline
  and abstraction gates pass. Full Audit passes (3288 jobs), with only
  permitted axioms.
  Complete large wrapper landed as `f1428d1`.
- Next: share forwarding/queue/native-return composition across the two
  proved fresh allocation routes, then large-route typed-header readback.
  Other allocator/object routes, ownership suppliers, collector closure,
  G2 and the ocamlc live-word budget remain open.

## Complete least-large-block wrapper (2026-10-04)

- `AllocLargeWrapper.allocate` proves actual wrapper entry, loaded indirect
  call, empty-list/zero-bitmap least-large-block allocation, successful
  header/accounting continuation and original caller return. Its
  postcondition retains exact memory, caller bank, stack and native frame.
- `BestFitFallback.StackConditions`/`MissingConditions` and
  `AllocLarge.Conditions` separate initial-memory geometry from machine
  entry facts. Snapshot transport lemmas supply the actual callee input.
- Targeted build passes (670 jobs); discipline and abstraction gates pass.
  Full Audit passes (3283 jobs), with only permitted axioms. Shared wrapper entry
  and original-caller restoration landed as `05cad7c`.
- Next: share fresh-oldify composition across allocation alternatives.
  Other allocator/object routes, ownership suppliers, collector closure,
  G2 and the ocamlc live-word budget remain open.

## Shared wrapper entry and original-caller restoration (2026-10-04)

- `AllocWrapperCore.enter` proves the wrapper prologue and loaded indirect
  call. `Entered.image` transports callee code images through its save log.
  `Entered.complete` restores the original caller bank, stack and PC from
  any proved `AllocFinish.Post`, with explicit free-log separation.
- `AllocWrapper.allocate` now instantiates this shared interface for the
  exact-size route. `AllocExact.Post.toFinished` adapts its existing
  postcondition; `AllocFinish.effect_of_memory` normalizes snapshots.
- FreshHeader regression passes (704 jobs); discipline and abstraction
  gates pass. Full Audit passes (3251 jobs); new headlines use only
  permitted axioms.
- Previous shared continuation landed as `0066655`. Next: pure large-route
  memory conditions, full large wrapper and fresh-oldify composition.
  G2, collector closure, ownership suppliers and the ocamlc live-word
  budget remain open.

## Shared wrapper continuation for both allocators (2026-10-04)

- `AllocFinish.CalleePost.finish` shares actual color selection, header
  and accounting stores, and native wrapper return across proved free-list
  callees. `header_of_effect`/`Post.header` share typed-header readback.
  The existing exact-size proof now uses these helpers.
- `AllocLarge.allocate` composes the complete least-large-block allocator
  with that continuation. `BestFitLargeFootprint.lean` derives preservation
  of wrapper code from every store in the large-block route. Conditions
  remain observations of explicit initial-memory write-log snapshots.
- Targeted large-route build (665 jobs), exact-size/fresh-route regression
  builds, full Audit (3178 jobs), discipline and abstraction gates pass;
  new headlines use only permitted axioms. Complete least-large-block
  allocation landed as `64fa050`.
- Next: share prologue/JALR and caller save-bank restoration, then extend
  the full wrapper and fresh-oldify route to the large-block alternative.
  Other allocator/object routes, ownership suppliers, collector closure
  and live-word Fits (G2) remain open.

## Complete least-large-block allocator alternative (2026-10-04)

- `BestFitLargeComplete.lean:allocate_large` proves actual allocator entry,
  empty exact-size list, zero filtered-bitmap search, least-large-block
  split, accounting and native return. The result restores the original
  caller PC and stack and retains exact combined memory, counter readback,
  code and native/output frame. `Allocated.requested` identifies the
  carved header using the original request recovered from the save bank.
- `BestFitLargeReturn.finish` supplies the generated accounting/return
  segment. Stack/header and caller-link separation remain explicit finite
  ownership obligations; no allocator run is assumed.
- Targeted build (640 jobs), full Audit (3175 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms.
  Allocator entry through split landed as `8788166`.
- Next: share the successful wrapper continuation across exact-size and
  least-large-block allocators, then extend the fresh-oldify composition.
  Other allocator/object routes, ownership suppliers, collector closure
  and live-word Fits (G2) remain open.

## Allocator entry through large-block split (2026-10-04)

- `BestFitFallbackLarge.lean:missing_large_split` composes the real
  allocator entry, empty-list classification, filtered-zero bitmap call,
  least-large-block tests and actual split callee. It retains the carved
  header, explicit combined log, stack, code and native/output frame.
- `SaveBank.Shape.read` shares native-bank geometry and readback across
  oldify, wrapper and fallback prologues. `Searched.saved` recovers the
  original request, bitmap and caller link after the real ffs call.
  Geometry for the split is stated on the explicit initial save snapshot.
- Targeted build (637 jobs), shared-bank/FreshHeader regression build
  (710 jobs), full Audit (3164 jobs), discipline and abstraction gates pass;
  new headlines use only permitted axioms. Least-large-block tests and
  split call landed as `d1fd3c8`.
- Next: final large-block accounting and native return, then reuse the
  wrapper continuation for this allocator alternative. Other allocator
  routes, ownership suppliers, collector closure and live-word Fits (G2)
  remain open.

## Least-large-block split call (2026-10-04)

- `BestFitLarge.lean:prepare` proves the saved-size/bitmap reload, actual
  nonnull least-block test, unsigned size test and pre-split native stores.
  `split` composes its decoded JAL with both proved `bf_split` paths and
  returns to the actual allocator continuation with the carved header,
  exact combined effects, unchanged stack, code and native/output frame.
- The generated `BestFitLarge` certificates take load/store stack offsets
  from the ELF and data addresses from Layout. `Conditions.of_memory`
  transports initial observations into real intermediate configurations.
  Stack/header separation is an explicit allocator-ownership obligation.
- Targeted build (625 jobs), full Audit (3127 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms. Empty
  exact-size-list entry through bitmap search landed as `7bb6cbd`.
- Next: compose the bitmap entry and split path, then the final accounting
  stores/native return. Nonzero bitmap/tree routes, ownership suppliers,
  collector closure and live-word Fits (G2) remain open.

## Empty-list entry through actual bitmap search (2026-10-04)

- `BestFitMissing.lean:missing_search_zero` starts at the real allocator
  entry, checks the small-size branch and empty exact-size list, executes
  the bitmap filter and decoded native saves, then the linking JAL and
  actual `ffs(0)` return. It reaches the fallback continuation with zero
  result, preserved stack, exact save log, code and native/output frame.
- `BestFitFallback.filtered_zero` derives the branch premise from a zero
  four-byte bitmap observation. All loads use total reads and concrete
  RAM windows; native offsets and instruction certificates are generated.
- Shared symbolic chunk/literal generation now handles LW, SLLW and AND.
  An initial broad simplification of the reflected write log exceeded
  practical memory use; the owned build was stopped and replaced with
  bounded explicit log normalization. No proof limits were raised.
- Targeted build (617 jobs), full Audit (3051 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms. The
  zero-input callee landed as `cc2457b`.
- Next: large-free-block tests, actual `bf_split` splice, accounting and
  native return. Nonzero bitmap/tree routes, ownership suppliers, full
  collector closure and live-word Fits (G2) remain open.

## Empty small-bitmap callee (2026-10-04)

- `FfsZero.lean:zero` proves the actual zero-input `ffs` call used by
  best-fit allocation: zero result, original return PC, unchanged memory
  and the complete native/output frame. `gen_gc_rows.py` now emits its
  ELF-derived code pins, function rows and zero-path certificates.
- Targeted build (602 jobs), full Audit (3044 jobs), discipline and
  abstraction gates pass. New headlines use only permitted axioms. Typed
  headers through the complete fresh queue route landed as `38f2b18`.
- Next: empty exact-size-list prefix, filtered bitmap/ffs call and
  large-block fallback, then reuse the proved `bf_split` and wrapper
  continuation. Nonzero size-search/tree routes, general heap ownership,
  collector closure and live-word Fits (G2) remain open.

## Typed header after the complete fresh route (2026-10-04)

- `FreshHeader.lean:header_of_allocation`, `Allocated.header`, and
  `Enqueued.header` prove the copied header retains the original typed
  size/tag through allocation, accounting and queue insertion, given
  explicit counter/header and queue/header separation.
- `AllocationConditions.header_address` derives nonwrapping header
  subtraction from the selected payload RAM window. `Enqueued.header_nat`
  exposes the natural-address form required by mopup. The shared wrapper
  header proof now consumes its exact memory effect independently of the
  platform postcondition.
- Targeted build (702 jobs), full Audit (3022 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms.
  The complete fresh queue route landed as `8f4cb30`.
- Next: extend allocator coverage beyond the exact-size fast path and
  connect the complete fresh route into mopup. The general ownership
  suppliers, other object routes, collector closure and live-word Fits
  (G2) remain open.

## Complete fresh scanned-object queue route (2026-10-04)

- `FreshEnqueued.lean:enqueue_fresh` executes real oldify entry, exact-size
  allocation, root update, source forwarding, pending-copy queue insertion
  and native return. It restores the original caller stack/registers and
  return PC, retains exact effects and output/native frame, and proves the
  updated root, queue links and copied first field.
- `Enqueued.payload` connects this complete route to the represented grey
  payload via `Eqv`; shared `pendingPayload_of_observations` also replaces
  the earlier segment-only payload proof. Saved-bank readback and queue
  condition transport are shared rather than duplicated.
- The explicit conditions still require free-list/heap/native-stack
  separation and preserve the original source suffix. These are geometry
  supplier obligations, not assumed allocator or oldify executions.
- Targeted build (701 jobs), full Audit (2990 jobs), discipline and
  abstraction gates pass; all new headlines use only permitted axioms.
  Fresh entry through allocation landed as `207164c`.
- Next: retain the typed allocated header and connect pending copies to
  mopup. Single-field/other-tag routes, larger/tree allocation, major-slice
  requests, collector closure and live-word Fits (G2) remain open.

## Fresh oldify through allocation (2026-10-04)

- `FreshAllocated.lean:allocate_fresh` composes actual oldify entry, argument
  preparation, allocating JAL and complete exact-size allocator return. It
  reaches `Enqueue.pc` with the allocated payload, original source/root,
  size and oldify stack pins, exact combined memory effects, preserved
  oldify code, output and native frame. No allocator execution is assumed.
- `AllocationConditions` names the remaining free-list/stack geometry on
  explicit initial-memory snapshots. `AllocationFootprint.lean` and
  `SaveBank.high` supply code preservation; memory-transport lemmas reuse
  these conditions at the actual intermediate configurations.
- Targeted build (692 jobs), full Audit (2989 jobs), discipline and
  abstraction gates pass. The new headline uses only permitted axioms.
  The complete wrapper landed as `146efff`.
- Next: compose the forwarding/queue insertion and original native return.
  Larger/tree allocation, major-slice requests, full collector closure and
  live-word Fits (G2) remain open.

## Complete exact-size allocating wrapper (2026-10-04)

- `AllocWrapper.lean:allocate` executes the actual wrapper prologue,
  function-pointer load, linking JALR, all exact-size small-list allocator
  branches, all color routes, and accounting/native return. It proves the
  original caller PC, stack and saved registers are restored, returns the
  selected payload, and retains exact combined effects and output/native
  frame. `Post.header` proves final `HeaderOk` for the original size/tag
  under the explicit header/counter separation condition.
- `SaveBank.read` shares the bounded native-bank argument between oldify
  and allocator saves. `AllocEntry.saved_after` supplies save/tag readback
  through separated free-list writes. The conditions remain initial
  observations of explicit write-log snapshots, with no callee-run premise.
- Targeted build (659 jobs) and full Audit (2970 jobs) pass, as do
  discipline and abstraction gates; new headlines use only permitted axioms. Exact-size
  free-list/continuation composition landed as `4d4e4b1`.
- Next: compose fresh oldify entry with this wrapper and the allocation-
  return queue/copy path. Larger-size/tree routes, major-slice requests,
  collector closure and live-word Fits (G2) remain open.

## Exact-size free-list entry through wrapper return (2026-10-04)

- `AllocExact.lean:allocate` composes every exact-size small-list branch
  with the actual wrapper continuation, covering every color-selection
  route. It proves the returned payload is the original selected list head,
  retains the combined exact write log, native save observations, return PC,
  output and native register frame. Conditions for the continuation are
  observations of a reflected memory snapshot, not assumed executions.
- `BestFitExact.effect_high` derives code preservation from every selected
  store location; `effect_of_memory` and shared `CoreConditions`/`Conditions`
  transport let the caller derive the allocator entry from the prologue.
- Targeted build (653 jobs), full Audit (2967 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms. All successful color continuations landed as
  `239d3a4`.
- Next: prologue/indirect-call composition and original caller save-bank
  readback, then fresh-copy completion. Larger-size/tree allocation, major
  slice requests, collector closure and live-word Fits (G2) remain open.

## Complete successful allocation continuation (2026-10-04)

- `AllocSuccess.lean:finish` proves all header-color paths from the actual
  return of a nonnull free-list call through native return, when the loaded
  accounting threshold selects no major-slice request. It composes
  `AllocSelect.select`, `AllocColor.prepare`, and `AllocAccount.account_return`.
  The post retains exact effects, initial native save observations, counter,
  output and native frame; `Post.result` returns the payload and `Post.header`
  proves final-memory `HeaderOk` under size/tag bounds and cell separation.
- The selector proves the real saved-tag load, phase LW, and conditional
  sweep-pointer load/unsigned comparison. Header construction proves both
  white/black size/tag encodings. Colors and phase constants are generated
  from the vendored runtime into Layout.
- Accounting and native-return conditions now have shared memory-transport
  lemmas so the read-only prefix supplies them from initial observations.
  No premise assumes a callee execution or future collector preservation.
- Targeted build (636 jobs), full Audit (2947 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Accounting-through-return landed
  as `8fc24fc`.
- Next: compose the actual free-list call and exact-size allocator with
  this continuation, then fresh-copy completion. Major-slice request,
  larger-block/tree allocation, collector closure and G2 remain open.

## Allocation accounting through native return (2026-10-04)

- `AllocAccountReturn.lean:account_return` composes actual header
  installation and allocated-word accounting with the allocator epilogue
  when the observed counter/threshold selects no major-slice request. It
  retains exact memory, initial saved-register observations, return PC,
  output, and native register frame. `ReturnPost.result` proves the ABI
  returns the payload pointer. `ReturnPost.header` reads the installed
  header under cell separation; `counter_nat` gives natural accounting
  under a no-overflow bound.
- `AllocAccountAccess.lean:access` supplies each store/load from RAM windows
  and total reads after the explicit first header store. The entry
  conditions contain no premise about a future machine execution.
- `AllocReturn.lean:return_machine` reuses the same native epilogue
  generator as oldify, including instruction-derived slots and stack
  adjustment; oldify generated output remains unchanged.
- Targeted build (616 jobs), full Audit (2941 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Both free-block split paths landed as `f051578`.
- Next: allocator header/color selection, free-list call composition,
  major-slice request and larger-block/tree routes. Fresh-copy completion,
  collector closure and live-word Fits (G2) remain open.

## Both free-block split paths (2026-10-04)

- `BestFitSplit.lean:56` (`split`) proves actual `bf_split` entry through
  native return on both remnant-size branches. The loaded source header
  determines the branch; the postcondition records the carved header
  address, exact counter/remnant-header stores, and preserved code.
- `BestFitSplitAccess.lean:7` and `:30` discharge memory access and branch
  obligations from initial RAM windows and observations. No future run
  or collector-preservation premise is assumed.
- `BestFitSplitGeometry.lean:delta_nat`, `remnant_header`, and `Post.remnant`
  prove the no-wrap remnant size and read the correctly sized/tagged header
  from final memory. `Post.counter` reads back accounting under explicit
  source-header separation. Free-list ownership remains a caller obligation.
- The existing symbolic chunk generator now supports RV64 shifts/add/sub
  and optional register composition through `SymbolicAppend`; this keeps
  the 13-instruction head certificate bounded without raising proof limits.
  White/abstract header constants come from generated `Layout`.
- Targeted build (608 jobs) and full Audit (2917 jobs) pass; new headlines
  use only permitted axioms. GC/Layout/argv
  generator drift, discipline (25 rules), and abstraction gates pass
  (C1=0, C2=7, C3=7, C4=3). Exact-size allocation landed as `5fcedd7`.
- Next: larger-size search/tree allocation,
  and outer-wrapper/fresh-copy composition. Full collector closure and
  live-word `Fits` (G2) remain open.

## All exact-size small-list allocation branches (2026-10-04)

- `BestFitExact.lean:allocate` covers all four combinations of cursor
  repair and empty/nonempty successor, from the actual function entry to
  native return. Its uniform result retains the returned header pointer,
  exact initial-memory-selected write log, free-word accounting and
  code/native/output frames. `Post.counter_nat` shares the common
  no-wrap credit argument.
- `BestFitEmpty.lean:prepare` derives the bitmap boundary from the actual
  size/head tests, selected cursor branch and empty-successor pop.
  `allocate` composes that prefix with `BestFitBitmap.clear_return`,
  framing the bitmap/counter observations back to entry memory.
- `CoreInput` shares the common initial allocator observations; optional
  repair and bitmap separation conditions apply only to their selected
  routes. Generated paths share existing block/access certificates.
- Capped targeted build (626 jobs), full Audit (2899 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Bitmap-through-return landed as `5ebd731`. Next: larger-size search and
  splitting, the large-block allocator, and outer-wrapper composition.
  Full free-list invariant preservation, fresh-copy completion, queue/root
  closure, ephemerons, major reclamation and G2 remain open.

## Empty-tail bitmap through native return (2026-10-04)

- `BestFitBitmapReturn.lean:clear_return` executes the actual bitmap block
  and shared accounting/native-return suffix. It proves the exact combined
  log, cleared bitmap, returned header pointer, and code/native/output
  frames. `Post.return_registers` and `Post.counter_frame` discharge the
  seam from the actual bitmap write and machine frame.
- `BestFitBitmap.lean:clear` and `cleared_word` show that the decoded
  LW/ADDIW/SLLW/AND/SW clears precisely the requested size-class bit.
  `mask_small` checks the fixed sixteen-class index independently of memory
  and bitmap contents. `BestFitFinish.lean:finish` packages the common
  accounting/return suffix with only its three required input registers.
- `Primitives/Word32Access.lean` shares total four-byte reads, LW/SW access
  windows, separated-write framing and truncated store readback. The
  generator supplies both block selections and their exact effects.
- Capped targeted build (619 jobs), full Audit (2868 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Both nonempty-tail cursor paths landed as `06f9cf9`. Next: compose the
  empty-tail entry/pop with this proved suffix, then large-block allocation
  and the outer allocation wrapper. Full free-list invariant preservation,
  fresh-copy completion, queue/root closure, ephemerons, major reclamation
  and G2 remain open.

## Best-fit merge-cursor repair (2026-10-04)

- `BestFitRepair.lean:allocate_nonempty` covers both merge-cursor branches
  for exact-size allocation with a nonempty successor. Initial memory
  determines the route. `allocate_repair` executes the repair store and
  shared pop/accounting/native-return suffix; `RepairPost.cursor` proves
  the cursor points back to the list-head cell. Head and accounting
  readbacks cover the repair path as well.
- `ChainCompose.lean:ChainAccess.append_eval` composes finite reflected
  access certificates. `BestFitChunks.lean` shares entry and pop/return
  certificates, and the existing unchanged-cursor proof now uses them.
  `BaseInput` shares initial observations; `NonemptyInput.repair` requires
  the additional store window/separation only when repair is selected.
- Capped targeted build (606 jobs), full Audit (2844 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. The first small-list path landed as `ca30886`. Next: empty-successor
  bitmap clearing, large-block allocation and wrapper composition. Complete
  free-list preservation, fresh-copy completion, queue/root closure,
  ephemerons, major reclamation and G2 remain open.

## Complete best-fit exact-size small-list path (2026-10-04)

- `BestFitSmall.lean:allocate` executes the real best-fit allocator from
  function entry through its native return for a nonnull exact-size list
  with a nonnull successor and an unchanged merge cursor. It proves the
  header-pointer return value, exact list-head/accounting stores, code
  preservation and complete machine frame. All premises are initial
  observations and memory windows, without a callee-run assumption.
- `Post.head` and `Post.counter` read back the actual stores.
  `Post.counter_nat` proves ordinary natural accounting when free-word
  credit covers the payload and header.
- `BestFitAccess.lean` discharges each actual access and branch. The
  generator emits the complete best-fit CFG/code pins and the selected
  path's register, log and return-PC certificates. Existing Layout provides
  all global/struct addresses and dimensions.
- Capped targeted build (603 jobs), full Audit (2827 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Indirect entry landed as `097d3e1`. Next: remaining small-list branches,
  then large-block allocation and composition with the wrapper's
  header/accounting/return. This one branch does not establish free-list
  invariant preservation or G2. Fresh-copy completion, queue/root closure,
  ephemerons and major reclamation remain open.

## Fresh entry executes the loaded free-list call (2026-10-04)

- `FreshIndirect.lean:enter_free_list` composes the complete fresh prefix
  with the actual indirect call. It retains the combined native-save/tag
  log, code images, output and register frame, and installs the allocator's
  return link at the loaded callee's entry.
- `AllocIndirect.lean:call_free_list` consumes the actual loaded pointer
  and its alignment. The generator emits JALR encoding/decode/pins; the
  existing `ret_tgt` lemma identifies its bit-cleared target.
- `Primitives/IndirectCall.lean:indirect_summary` and
  `Vsa/Sim/JalrBridge.lean:jalrCallFacts_of_obs` share the existing direct-call
  bridge and generic register frame. No callee execution is assumed.
- Capped targeted build (656 jobs), full Audit (2757 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Allocator prefix landed as `8897f51`. Next: the actual
  free-list allocation body, followed by header/accounting and return.
  Fresh-copy completion, queue/root closure, ephemerons, major reclamation
  and G2 remain open.

## Fresh entry through the free-list call boundary (2026-10-03)

- `FreshAllocator.lean:prepare_free_list` composes real oldify entry, its
  allocating JAL and the allocating wrapper's prologue. It yields the
  exact combined native-save/tag log, loaded free-list target and outgoing
  register interface, preserving both code images and output/native frames.
  `AllocationEntry.allocator_input` derives the wrapper input from initial
  windows and framed global observations; `allocator_size` discharges the
  maximum-size branch for any source header.
- `AllocEntryAccess.lean:prepare` executes the size branch, native stores
  and actual function-pointer load. `gen_gc_rows.py` emits all allocator
  segments/code pins plus the selected prefix certificates. Per-block
  register/log equations keep save-log certification small.
- `gen_layout.py` supplies the free-list function-pointer and GC-phase/sweep
  symbols and minor-heap-size offset. All accesses use Layout.
  `OldifyEntry.saveLog_high` shares the store-policy argument with the
  existing whole forwarded call.
- Capped targeted build (649 jobs), full Audit (2734 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Fresh allocation-entry proof
  landed as `af7e654`. Next: execute the indirect free-list call and prove
  allocation/header/accounting/native-return paths. Fresh-copy completion,
  full queue/root closure, ephemerons, major reclamation and G2 remain open.

## Fresh scanned-object entry reaches allocation (2026-10-03)

- `FreshCall.lean:prepare_allocation` executes the actual oldify prologue,
  strict nursery tests, nonzero-header/scanned-tag classifier, argument
  setup and JAL into `caml_alloc_shr_for_minor_gc`. It preserves the exact
  native save log, original caller values, output/native frames and update
  context, and establishes the allocator's actual return link.
- `FreshAccess.lean:header_conditions` derives the branch facts from
  HeaderOk, positive size and a tag below Infix_tag.
  `Prepared.typed_arguments` identifies the real ABI size/tag/header words.
  `FreshEntry.lean:prepare_entry` retains the separately usable pre-JAL cut.
- `scripts/gen_gc_rows.py` now emits the fresh prefix and allocating call
  certificates from the pinned ELF, including the prologue's tag limit.
  Targeted build (644 jobs), full Audit (2713 jobs), generator drift,
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Mixed queue traversal landed as `d9ee4b8`.
- The allocation body is still open: reaching its entry is not a completed
  fresh copy. Next: connect its real allocation/update result to the proved
  enqueue/native-return path. Other first-child cases, full queue/root
  closure, ephemerons, major reclamation and G2 remain open.

## Pending-object traversal with a mixed suffix (2026-10-03)

- `PopMixed.lean:pop_mixed` and `resume_mixed` execute initial/backedge
  queue visits through first-child forwarding, setup and a complete mixed
  suffix. The result includes relocated ObjAt, the remaining queue, and
  memory/native/code/output frames. `MixedPending` contains only initial
  platform, heap, geometric and typed-relocation observations.
- `MixedMemory.lean:LoopData.frame` preserves the suffix's values and route
  decisions across separated earlier writes. `MixedSetup.lean` derives the
  real setup boundary and composes it with the complete mixed scan.
- Shared `ForwardedField.setup_result`,
  `PopFirstPost.traversal_result` and `first_outside_of_stack` handle both
  traversal variants. Existing forwarded-only proofs now instantiate them.
- Capped targeted build (725 jobs), full Audit (2704 jobs), discipline and
  abstraction gates pass; new headlines use only permitted axioms.
  Mixed suffix landed as `2fe46be`.
  The first child is still required to be already-forwarded young; suffix
  fields may be immediate, non-young or already-forwarded young. Fresh-copy
  allocation, remaining first-child cases, outer roots/queue closure,
  ephemerons, major reclamation and G2 remain open. Next: extend the fresh
  oldify paths and their partial-relocation suppliers.

## Mixed copied/forwarded suffix (2026-10-03)

- `MixedField.lean:step` executes either the real immediate/non-young copy
  or complete already-forwarded young oldify route. `CopyNonYoung.lean`
  shares the copy branch selection with the existing non-young loop;
  `CopyContext.lean` retains its native interface and oldify code image.
- `MixedLoop.lean:mixed_scan` folds these steps with the observed index.
  `MixedLoopState.lean:LoopAt.input` derives each actual input from initial
  heap facts and memory frames; `LoopAt.route` proves parity/range decisions
  agree with the framed initial observations. `MixedSchedule.lean` supplies
  canonical register maps and proves their transition law from initial data.
- `MixedRelocated.lean:scan_relocated` yields ObjAt at the new placement
  through shared Eqv transport. `LoopAt.initial` initializes the invariant
  from platform/code/register pins. Existing forwarded-only clients use the
  same generic `RelocatedResult` interface.
- Capped targeted builds (686 and 722 jobs), full Audit (2655 jobs),
  discipline and abstraction gates pass; new headlines use only permitted
  axioms. Backedge traversal landed
  as `1c6a83d`. Next: compose mixed setup/queue seams, then extend fresh-copy
  allocation coverage. Fresh young objects, outer roots, ephemerons, major
  reclamation and G2/live-word Fits remain open.

## Forwarded traversal from the queue backedge (2026-10-03)

- `QueueForwarded.lean:resume_forwarded` executes a subsequent queue visit
  through the complete already-forwarded object traversal. Initial and
  backedge entries share `first_after_pop` and `forwarded_after_first`;
  each retains its own generated pop certificate.
- `CopyProgress.lean:CopyEffect.progress` normalizes either verbatim-copy
  route into the shared progress interface with arbitrary containing
  footprint and expected values. The existing scan update now uses it;
  integer queue composition also reuses `frameOn_comp`.
- Capped targeted build (718 jobs), full Audit (2645 jobs), discipline and
  abstraction gates pass. New headlines use only permitted axioms.
  Whole initial traversal landed
  as `5464f8e`. Next: combine verbatim and forwarded field routes under one
  loop invariant. Fresh-copy/allocator paths, outer roots, ephemerons,
  major reclamation and G2 remain open.

## Complete forwarded pending-object traversal (2026-10-03)

- `PopForwarded.lean:pop_forwarded` composes queue pop, first-child oldify,
  native return, suffix setup and the terminating forwarded suffix. It
  yields ObjAt at the relocated placement, preserves the remaining queue,
  and supplies memory, native, code and output frames. Intermediate inputs
  are derived from execution and initial observations.
- `PopFirstFootprint.lean` bounds the concrete prefix log by the queue-head,
  native-save and first-slot windows. `PopFirstSetup.lean` derives setup and
  typed grey inputs; `QueueWindows.lean:View.frame_windows` and shared
  `Vsa.Sim.frameOn_comp` compose the memory/queue frames.
- Capped targeted build (713 jobs) and full Audit (2635 jobs) pass; new
  headlines use only permitted axioms. Discipline and abstraction gates pass.
  Setup landed as `76bf838`.
  This covers objects with more than one field whose children are all
  already-forwarded young values. Mixed/fresh-copy cases, allocator
  suppliers, outer roots, ephemerons, major reclamation and G2 remain open.
  Next: share this continuation with the outer queue backedge, then extend
  the collector coverage.

## Suffix setup through typed forwarded scan (2026-10-03)

- `ForwardedSetupContext.lean:setup_initial` derives the complete loop
  context from the actual setup result and preserved native pins.
  `ForwardedSetup.lean:setup_relocated` composes setup with the terminating
  forwarded suffix, yielding ObjAt at the new placement and memory/native/
  code/output frames relative to the original pre-setup boundary.
- `ForwardedMemory.lean:LoopData.frame` transports fixed suffix observations
  across an arbitrary separated earlier write footprint. Read-only
  `LoopData.memory_eq` is its empty-footprint instance. The relocated grey
  boundary has a matching memory-identity transport.
- Capped targeted build passes (695 jobs). Queue-pop/first-field composition
  landed as `8cf9edb`; PHASES records the setup seam. Next: derive the
  combined queue/native/first-slot footprint and connect both halves into
  a complete pending-object traversal. Mixed/fresh-copy cases, allocator
  suppliers, outer roots, ephemerons, major reclamation and G2 remain open.

## Queue pop through forwarded first-field update (2026-10-03)

- `QueueObserved.lean` supplies concrete source/copy/child pins and the
  canonical queue-head store. `QueueFirstInput.lean:PopPost.first_input`
  derives the callee-facing input from those loads, preserved native pins
  and framed initial observations; `first_pc` uses the actual parity test.
- `PopFirst.lean:pop_first` composes the actual pop and complete forwarded
  first-field path, with exact combined log, restored native state, code
  and output frames, and remaining queue. `View.frame_log` shares the queue
  Eqv frame; the older forwarded-slot proof now uses it too.
- `PopFirstPayload.lean:PopFirstPost.relocating_grey` supplies the typed
  suffix boundary. Shared `relocating_grey_of_pending` also serves the
  standalone first-field result. Existing integer-pop setup now reuses
  the same concrete loaded-pointer facts.
- Capped targeted build passes (705 jobs). First-field update landed as
  `7e70e0b`; PHASES records the queue-pop seam. Next: suffix-setup and whole
  pending-object composition, mixed fields and fresh-copy/allocator cases.
  Outer roots, ephemerons, major reclamation and G2/live-word Fits remain open.

## First-field update and relocated grey boundary (2026-10-03)

- `FirstArgs.lean:args_machine` executes the generated destination setup.
  `FirstField.lean:forwarded` composes actual nursery tests, that setup,
  JAL, the complete forwarded oldify callee and return jump to suffix setup.
  It proves exact native-save/first-slot writes, restored registers, code
  and output preservation, and the restricted native ABI frame.
- `FirstPayload.lean:Post.first_relocates` uses Eqv to interpret the actual
  store. `Post.relocating_grey` supplies the typed suffix boundary: first
  field at the new placement, separated source suffix at the old placement.
  It requires the actual loaded child and typed forwarding observation.
- Capped targeted build passes (694 jobs). Classifier work landed as
  `544989b`; PHASES records the first-field route. Next: queue-pop and
  suffix-setup seams, then mixed fields and fresh-copy/allocator cases.
  Outer roots, ephemerons, major reclamation and G2/live-word Fits remain open.

## First-field nursery classifier (2026-10-03)

- `FirstYoungAccess.lean:classify` proves the actual first-field strict
  nursery tests. It shares `Young.classify_site` with the suffix site,
  retaining each site's generated fetch/decode and endpoint certificates.
- `AccessRetarget.lean:ChainAccess.retarget` folds finite scalar certificates
  across reflected block equivalence. The generator proves first/suffix
  access, control and symbolic-data equivalence by reduction; there is no
  duplicated scalar-load or branch proof and no assumed machine run.
- Capped targeted build passes (683 jobs), including the full typed suffix
  proof after refactoring. Shared call/return work landed as `e90d6c9`.
  Next: first-field destination argument setup and classifier/call composition.
  Fresh-copy/allocator routes, mixed fields, outer roots, ephemerons, major
  reclamation and G2/live-word Fits remain open.

## Shared oldify bridge and first-field call (2026-10-03)

- `OldifyBridge.lean:forwarded` and `OldifyResume.lean:forwarded_resume`
  share the actual JAL/callee/return-jump proof across generated call sites.
  The existing suffix APIs instantiate these certificates and the complete
  typed suffix proof still builds. Native restoration/ABI framing is shared.
- `Generated/FirstCall.lean` is emitted by `gen_gc_rows.py` from the
  distinct first-field JAL and its jump to suffix setup.
  `FirstForwarded.lean:forwarded_resume` proves that complete call route
  for an already-forwarded child, with exact writes/restored registers.
- Capped targeted build passes (682 jobs); generator check passes. Typed
  relocated object result landed as `9f16402`. Next: first-field nursery
  classifier and argument setup, then the first-field representation seam.
  Fresh copying/allocation, mixed routes, outer roots, ephemerons, major
  reclamation and G2/live-word Fits remain open.

## Typed relocated payload and initialization (2026-10-03)

- `RelocatedPayload.lean:ScanAtWith.relocated_payload` transports completed
  suffix words through Eqv to the new placement; `relocated_object` adds
  the framed target header. `RelocatingGrey` names the already-handled
  first field and original-placement source suffix boundary.
- `ForwardedField.scan_relocated` composes the actual forwarded loop with
  that typed result, yielding ObjAt at the relocated placement. The typed
  forwarding action and first-field boundary remain heap obligations.
- `ForwardedInitial.lean:LoopAt.initial` derives the starting invariant
  from concrete platform/code/register pins. The existing generic scan
  initializer now accepts arbitrary footprints and expected field words.
- Capped targeted builds pass (689 jobs). Full forwarded loop landed as
  `47bcf2a`; PHASES records the typed completion. Next: mixed field routes,
  first-field handling, and fresh copying/allocation. Outer roots,
  ephemerons, major reclamation and G2/live-word Fits remain open.

## Complete already-forwarded suffix loop (2026-10-03)

- `ForwardedLoop.lean:forwarded_scan` executes every loaded-field/classifier/
  oldify/advance iteration to suffix completion. `LoopAt.step` preserves
  the relocated scan, oldify image and next native register view.
- `ForwardedLoopState.lean:LoopAt.input` derives each call input from
  fixed initial field/domain/header observations and the accumulated write
  frame. `LoopData` contains geometric and value facts, not machine-run
  premises. The loop covers already-forwarded young fields only.
- Shared `Vsa.Sim.indexedLoop` factors the observed-counter termination
  proof, and the original `ScanAtWith.loop` now instantiates it. Existing
  mixed-copy payload still builds. `Input.scan_progress` shares the
  concrete iteration adapter between the bare and context-carrying proofs.
- Capped targeted builds pass (677 jobs for the full forwarded loop; 688
  for loop state plus existing mixed payload). Context work landed as
  `f3af688`. PHASES records this discharged subcase. Next: typed relocated
  payload, mixed young/non-young fields, and fresh-copy/allocator routes.
  Roots, ephemerons, major reclamation and G2/live-word Fits remain open.

## Forwarded iteration context preservation (2026-10-03)

- `ForwardedContext.lean:Input.oldifyCode_after` preserves the oldify image
  from actual native/destination windows. `Input.next_registers` supplies
  the next field boundary with advanced source/index, installed return link
  and restored native values. Input no longer asks for x10/x11 pins that
  the classifier overwrites.
- `ObservationFrame.lean:frame_word` shares observation preservation for
  arbitrary write windows; the old singleton scan helper now uses it.
  `ForwardedObservations.lean:Conditions.frame` preserves the four runtime/
  forwarding-header reads needed by the call under this frame.
- Targeted capped builds pass (672 jobs for context, 644 for observation
  transport). Concrete iteration landed as `c08c9e3`. Next: construct a
  loop invariant retaining this context and derive each field input from
  initial observations, then fold the actual forwarded-field iterations.
  Fresh-copy/allocator paths, roots, ephemerons, major reclamation and
  G2/live-word Fits remain open.

## Concrete forwarded scan iteration (2026-10-03)

- `ScanFootprint.lean:effect_entry` bounds every native save with the
  generated slot offsets and separates the one destination store.
  `scanFootprint_of_geometry` derives all scan footprint obligations from
  one native-stack/object separation condition and object geometry.
- `ForwardedIteration.lean:scan_iteration` runs the actual field load,
  classification, forwarded oldify call and advance, then updates
  `ScanAtWith` with the relocated destination value. The caller supplies
  the forwarding observation and geometric/platform entry conditions,
  not a machine execution or per-store separation certificates.
- Capped targeted build passes (670 jobs). Shared generalized scan landed
  as `7887a5c`. Next: maintain the callee input and forwarding observations
  across loop iterations and cover fresh-copy cases. G2/live-word Fits,
  allocator/freshness, roots, ephemerons and major reclamation remain open.

## Relocated field observations and shared scan update (2026-10-03)

- `ForwardedEffect.lean` proves `AdvancedPost.word_frame` from the actual
  save/root log, `slot_relocates` via Eqv, and `againAfterCall_count` from
  header separation and size. These discharge observation consequences of
  the concrete call rather than assuming memory is unchanged.
- `ScanAtWith` now parameterizes the permitted footprint and expected field
  words, with the original copying interpretation as defaults. Its shared
  `loop` works for both interpretations. `ScanProgress` and
  `advance_progress` factor the invariant update; existing copy proofs use
  them and still build.
- `ForwardedScan.lean:AdvancedPost.progress` turns a forwarded-field run
  into that same scan update, retaining platform/code/output/native frames.
  `ScanFootprint` names the remaining native-save/header/prefix separation
  facts supplied by the enclosing heap and stack geometry.
- Targeted capped builds pass (668 jobs for the forwarded adapter; 655 for
  the existing mixed payload proof). Loaded-field composition landed as
  `d3d4cc1`. Next: supply these footprints and forwarding values from a
  partial-relocation scan invariant and close the mixed young-field loop.
  Fresh copying/allocation, roots, ephemerons, major reclamation and the
  G2/live-word Fits exit remain open.

## Loaded forwarded field through advance (2026-10-03)

- `ForwardedField.lean:forwarded_field` composes the actual source-field
  load, parity and nursery tests, mopup call, complete forwarded oldify
  invocation, return jump and header advance. The destination argument is
  computed by the classifier; its stored word is the source forwarding
  target. Exact native-save/root logs and platform/code/output frames hold.
- `ForwardedCall.Conditions.memory_eq` separates geometric/value conditions
  from the register/platform input established by the read-only classifier.
  The result retains the installed return link and a restricted ABI frame.
- Targeted capped build passes (658 jobs). Advance/ABI work landed as
  `29c0ac5`. Next: establish header-size preservation and typed relocation,
  then include this case in the scan invariant. Fresh allocation, roots,
  ephemerons, major reclamation and G2/live-word Fits remain open.

## Forwarded-field header advance and ABI frame (2026-10-03)

- `ForwardedAdvance.lean:forwarded_advance` runs the actual mopup JAL,
  forwarded callee, return jump and header/counter advance. The destination
  contains the forwarding target; source/index increase once; the branch
  uses the actual post-call header. Its exact log includes native saves.
- `Advance.lean:advance_machine` shares the advance independently of a
  preceding copy. Existing copy proofs now use the same generic header-load
  certificate and generated control equivalence; no duplicate store is run.
- Shared `lookupG_eraseG_ne` normalizes reflected symbolic register tails.
  `frame_of_restored` recovers an ABI frame from original/restored pins;
  `MopupCall.abi_frame` reduces the whole call to x1/x12/x14/x15 clobbers.
  The advanced result additionally permits only x8/x9, so the scan can retain
  its callee-saved domain and payload registers.
- Targeted capped build passes (655 jobs). Mopup call/resume landed as
  `16d9a00`. Next: compose the field read/classifier with this call route,
  supply size preservation from footprints, and connect typed relocation.
  Fresh copying/allocation, general relocation loop, roots, ephemerons,
  major reclamation and G2/live-word Fits remain open.

## Mopup call and returned forwarded field (2026-10-03)

- `MopupForwarded.lean:forwarded` uses the shared direct-call bridge and
  an ELF-generated JAL certificate, invokes the proved already-forwarded
  oldify callee, and returns to mopup with its installed link address.
- `MopupResume.lean:forwarded_resume` includes the real post-return jump
  to the header/counter advance. It retains the exact native-save/root log,
  relocated destination word, restored native/scan registers and complete
  platform/output/code frames. The pointer still must have a zero forwarded
  header; no allocator or fresh-copy case is assumed.
- `image_writeLog` shares image preservation for composed exact logs.
  `ForwardedCall.Input.effect_high` supplies the above-HTIF footprint from
  the real write windows, proving mopup code survives the callee.
- Targeted capped build passes (650 jobs). Whole oldify call landed as
  `1e683fa`. Next: discharge the header-controlled advance after this call
  and compose the loaded-field classifier with the forwarded route. General
  copying/allocation, relocation loop, roots, ephemerons, major reclamation
  and G2/live-word Fits remain open.

## Whole already-forwarded oldify invocation (2026-10-03)

- `ForwardedCall.lean:forwarded_call` composes the concrete pointer-entry
  prologue, both nursery-bound tests, zero-header path, root store and
  native return. It proves the original return PC/caller registers, exact
  native-save-plus-root log, updated root and platform/code/output frames.
  No callee-run or saved-load identity is assumed.
- `OldifyYoung.lean:young_machine` discharges both strict-young branches
  from actual Layout-based domain reads and bounds. `OldifyCallSeams`
  carries the root/stack registers and supplies its input from the prologue.
- `ForwardedCall.Input` names the native/domain/source/root separation
  footprints. The caller must supply these geometric facts, source header
  zero and young/even classification; allocation is not part of this route.
- Targeted capped build passes (642 jobs). Prologue/saved frame landed as
  `b3b23f4`. Next: splice this callee into the mopup young-field call and
  handle its relocated field result. Fresh copying/allocation, general
  partial relocation, roots, ephemerons, major reclamation and G2 remain open.

## Concrete oldify pointer entry and saved frame (2026-10-03)

- `OldifyEntry.lean:entry_machine` executes the non-immediate prologue
  through the nursery-range-test PC: all eleven native saves, argument
  moves and runtime constants, with exact log and complete machine frame.
  The parity branch follows from the concrete argument, and all writes
  follow from decoded-slot RAM windows.
- `OldifySaved.lean:Post.saved` reads back each original caller register.
  `Post.restored_caller` and `Post.returnWord` identify the common epilogue
  interface and return target with the caller values. The generator checks
  that save/restore slots agree and proves their finite separation.
- `word_writeLog_cells` shares separated-bank readback; `stack_bound` and
  `stack_address` keep modular arithmetic over an abstract pointer. The
  frame bound follows from an actual RAM window. Direct generated log
  certificates avoid expensive simplification of the decoded negative
  adjustment; default proof budgets are unchanged.
- Targeted capped build passes (614 jobs). Queue insertion/return landed
  as `acdad34`. Next: oldify nursery-range tests and whole forwarded-call
  composition, then young-field caller splicing. Allocation, full partial
  relocation, roots, ephemerons, major reclamation and G2 remain open.

## Queue insertion through native return (2026-10-03)

- `EnqueueReturn.lean:enqueue_return` composes the concrete six-store
  insertion with the common epilogue. The result retains the new queue node,
  root and saved first field, exact write log, restored native registers,
  caller return address and output/code/platform frames. The allocating
  call itself remains open.
- `EnqueueRunPost.memory_effect` identifies the actual scalar reads with
  the original source first word and queue head. `SavedSame.of_writeLog`
  shares the native-stack framing argument across both writing paths;
  the read-only epilogue transports queue observations through Eqv.
- Targeted capped build passes (622 jobs). Native return landed as
  `680ec74`. Next: concrete oldify prologue and range-entry seams, then
  young-field caller composition. Allocator/freshness, full partial
  relocation, roots, ephemerons, major reclamation and G2 remain open.

## Oldify native return and forwarded composition (2026-10-03)

- `OldifyReturn.lean:return_machine` proves the common native epilogue
  from concrete stack windows and an aligned saved return address. All
  eleven loads restore their saved registers, sp advances by the decoded
  frame size, memory/output remain unchanged, and execution returns.
- The generator extracts saved slots and the stack adjustment from the ELF.
  Access certificates use ordered load facts rather than backtracking over
  concrete memory terms; all proofs retain the default elaboration limit.
- `ForwardedReturn.lean:forwarded_return` composes the real zero-header
  path through that epilogue. It retains the root store, restored registers,
  original saved return address, platform/code/output and native frames.
  `SavedSame` shares the saved-word frame interface for further call seams.
- Targeted capped build passes (617 jobs). Forwarded root update landed
  as `a99f02d`. Next: prologue/range entry and caller composition, plus
  allocation-return restoration. Full collector relocation and G2 remain open.

## Already-forwarded oldify path (2026-10-03)

- `ForwardedAccess.lean:forwarded_machine` runs the generated zero-header
  branch, forwarding-pointer load and root store, stopping at the native
  epilogue. All reads, the branch and store are discharged from concrete
  windows/registers/header facts. The full BlockPost retains machine frames.
- `Post.slot_relocates` transports an actual root slot through Eqv once the
  partial-placement invariant identifies the forwarding pointer with the
  typed action. `Post.target_from_links` consumes the existing intrusive
  link view; `Post.queue_frame` preserves a disjoint queue.
- `CodeFrame.image_after` shares preservation below the store-policy bound
  between oldify and mopup code images. Generated helper certificates and
  audit entries come from `scripts/gen_gc_rows.py`.
- Targeted capped build passes (614 jobs). Mixed scan landed as `a31aa63`.
  Next: oldify entry/return seams and young-pointer call composition, then
  remaining copying/allocation paths. Partial relocation, roots, outer
  termination, ephemerons, major reclamation and G2/live-word Fits are open.

## Mixed non-young field scan (2026-10-03)

- `MixedScan.lean:mixed_scan` runs the whole suffix with a fresh parity/range
  decision at each field. Even non-young words use the new classifier/store
  path; immediates use the existing shorter path. `DomainFrame` records the
  three runtime-word footprints that must remain separate from the copy.
- `MixedPayload.lean:scan_mixed_grey` gives ObjAt after that real loop.
  `pending_nonYoung` supplies branch safety from NoForgery for nonpointers
  and explicit non-young placement of genuine pointer fields. Young pointers
  requiring relocation remain outside this theorem.
- `ScanAtWith` parameterizes only the native write set. `ScanAt` retains the
  original five-register interface. `ScanAtWith.advance` shares the copy
  invariant update, and `ScanAtWith.loop` shares the standard loop fold.
  Existing integer theorems and downstream queue summaries still build.
  The grey-payload Eqv proof is shared through `ScanAtWith.payload/object`.
- Targeted capped builds pass. Non-young even copying landed as `6d91b28`.
  Next: young-pointer oldify paths and partial-relocation composition; mixed
  setup/queue seams, outer termination, allocator freshness, ephemerons and
  full G2/live-word Fits remain open.

## Non-young even-field copy (2026-10-03)

- `CopyEffect.lean:copy_even` composes the real field read/tag branch, range
  tests, copy store and header-controlled advance. From concrete non-young
  bounds it proves the copied word, single-store footprint, counter/source
  increments, final PC and memory/output/native frame.
- `FieldStore.lean:store_machine` reuses the existing store and tail access
  proofs. The shared continuation register order and normalized single-store
  log let those proofs apply directly, without raising elaboration budgets.
- `CopyEffect` exposes the common loop-step result with an explicit write set.
  `CopyPost.effect` retains the immediate path's stronger five-register frame;
  the even path additionally permits its actual a4 classifier write.
- Targeted capped builds pass. Loaded-field classification landed as
  `8c1424e`. Next: share the scan invariant update and fold mixed non-young
  fields. Young-pointer oldify calls, outer queue termination, allocation,
  ephemerons and full G2/live-word Fits remain open.

## Loaded-field classification (2026-10-03)

- `FieldClassify.lean:classify_field` composes the actual field read, parity
  branch and range classifier. The result selects the copy or oldify PC from
  concrete bounds and preserves the loaded value, destination pointer and
  loop-carried registers, with exact memory/output/native frames.
- `FieldRead.lean:read_machine` covers both low-bit outcomes with a single
  total source read. `ReadPost.young_input` supplies the range classifier
  from the preserved runtime register and domain memory.
- `ClassifiedPost.copy_nonpointer` derives the copy route from NoForgery.
  Evenness supplies the first branch; no branch/run oracle is introduced.
- `Vsa/Sim/GRegsFrame.lean` shares register-interface selection and transport
  through the existing complete frame; this avoids new per-register cases.
  `head_access_bytes` shares the first-read access certificate with the
  already-landed integer-copy path.
- Targeted capped builds pass. Young-range classification landed as `a4046ad`.
  Next: compose the store/advance continuation and oldify call. Full outer
  queue termination, allocation, ephemerons and G2/live-word Fits remain open.

## Concrete young-range classifier (2026-10-03)

- `YoungAccess.lean:117` (`Young.classify`) runs both range-test blocks from
  concrete total reads of Caml_state, young_end and young_start. Every symbol
  and field offset comes from Layout. Its exact endpoint is oldify only when
  `young_start < value < young_end`; otherwise it reaches the copy store.
- The classifier is memory/output preserving and writes only a4/a5. Generated
  code/shape/effect certificates cover all three paths; the input supplies
  platform/register pins, the represented domain pointer and RAM windows.
- `decision_at_start` and `decision_at_end` check both excluded endpoints.
  `nonpointer_outside` and `Result.copy_nonpointer` connect the actual strict
  classifier to the existing conservative half-open NoForgery invariant.
  The caller still supplies parity; young-pointer oldification is open.
- Targeted build and full axiom audit pass under the 24 GB cap. Empty queue
  exits landed as `8e66983`. Next: compose non-immediate field paths and oldify
  calls. Outer queue termination, allocation, ephemerons and G2 remain open.

## Empty queue exits (2026-10-03)

- `QueueEmpty.lean:empty_machine` certifies both the initial and bottom empty
  tests, using a total read of the Layout-derived queue-head word. Both reach
  ephemeron processing with memory and output unchanged; the full kernel
  register frame is retained.
- `PopScanPost.empty_input` derives this concrete input after the last integer
  block, including the preserved global-head register. The generated helper
  certifies code, chain shape, no stores, the sole written register and exit PC.
- Targeted capped build passes. The repeated nonempty entry landed as
  `f80d34e`. Queue invariants/termination, pointer classifiers and oldify calls,
  ephemerons, allocation and full G2/live-word Fits remain open.

## Queue back-edge entry (2026-10-03)

- `QueueResume.lean:resume_scan` certifies the actual bottom queue test and
  composes it with the existing represented scan continuation. Both initial
  and subsequent visits now have concrete entry summaries.
- `Generated/MopupPop.lean:resume_effects` proves that the two entry paths
  have the same complete effects after rejoining the shared child block.
  The resume path gets its own code/shape/access/branch certificates; it does
  not reuse a run from a different PC. `scan_after_pop` factors the common
  continuation without duplicating the field-loop proof.
- Targeted capped build passes. The first queue-pop/scan composition landed
  as `93acf8e`. Remaining: outer queue invariant/termination and empty exit,
  pointer classifiers/oldify calls, allocation and full G2/live-word Fits.

## Queue pop through represented integer block (2026-10-03)

- `PopScan.lean:180` (`pop_scan`) composes the concrete queue pop, saved-first
  classifier, setup and complete integer suffix. Its post gives ObjAt, the
  remaining queue, exact write footprint (global head and destination suffix),
  unchanged output, unaffected registers and platform/code/exit pins.
- `PopPost.setup_input` derives the setup pointers from the actual loads and
  preserves the runtime s8 constant with the segment kernel frame. PopPost now
  retains the complete BlockPost alongside its reflected machine result.
- `PayloadOutsideTodo` and `QueueOutsideScan` name the word-footprint facts
  expected from heap ownership. `PopPost.payload` and `View.scan_frame` use
  Eqv transport; shared `body_frame_words` handles both logs and loop frames.
- `CodeFrame.lean:mopupCode_after` shares code-image preservation across both
  paths, replacing the formerly local field-copy argument.
- Targeted capped build passes. Setup/scan composition landed as `6a1797a`.
  This proves one pending block with integer fields. Outer queue back-edge,
  pointer classification/oldify calls, allocation and full G2 remain open;
  production Fits and the compiler GcSafe obligation remain unchanged.

## Machine setup through represented scan (2026-10-03)

- `ScanSetup.lean:setup_scan` composes the actual mopup setup block with the
  complete integer-suffix loop and its ObjAt result. `setup_access` derives
  the header load and unsigned size branch from RAM geometry and the represented
  multi-field header. `setup_machine` establishes every initial scan pin.
- `ScannedObject` retains the resulting platform/code state, exit PC, object,
  memory frame outside the destination suffix, unchanged output and composed
  register frame. The generator emits setup shape, code, no-store, register
  and exit certificates directly from the ELF CFG.
- This starts after the saved first field is handled. Queue-pop composition,
  pointer classifiers and oldify calls, allocator freshness and full G2 remain
  open. Production Fits still counts allocated words; compiler GcSafe is open.
- The typed payload bridge landed as `ef15613`.

## Typed scan result (2026-10-03)

- `ScanPayload.lean:scan_grey` combines the concrete suffix loop with
  `pendingPayload` to establish a represented destination block (`ObjAt`).
  `ScanAt.payload` uses Eqv.val transport for each field; `ScanAt.object`
  preserves the destination header, including its existing color.
- `pending_immediates` derives every low-bit branch from represented integer
  fields. `ScanAt.initial` supplies the empty-prefix/reflexive-frame invariant
  from setup pins. The saved first word lies outside the scanned suffix.
- This result keeps the placement fixed and requires integer suffix fields.
  Pointer oldification and machine setup composition remain open, alongside
  full mopup/G2, live-word Fits and compiler GcSafe.
- Targeted capped build passes. The suffix loop landed as `628af1d`.

## Immediate-field scan loop (2026-10-03)

- `ScanLoop.lean:scan_loop` folds the actual immediate-valued field iterations
  with `loopFromBody`, decreasing the remaining word count. `ScanAt` records
  the destination suffix frame, copied prefix, loop registers, code, output
  and unaffected native registers. No run or branch oracle is assumed.
- `ScanGeometry.lean:again_eq` derives the real back-edge decision from the
  preserved size header. RAM geometry supplies every iteration window; source
  disjointness preserves the original field observations.
- The capped targeted build passes. The previous single-iteration and shared
  code-frame increment landed as `fd33bad`.
- Next: connect grey payloads to the scan result and compose pointer oldify
  calls. Full mopup, allocator freshness, G2/live-word Fits and compiler
  GcSafe remain open.

## Immediate-field mopup iteration (2026-10-03)

- `Generated/FieldCopy.lean` composes the actual load/test, store and advance
  blocks with both final-field and loop-back outcomes. It proves the single
  destination store, counter/source-pointer increments and all loop-carried
  register pins. The generator supplies fetch/decode certificates and exit PCs.
- `FieldCopyAccess.lean:copy_machine` supplies every scalar access and branch
  fact from RAM windows, concrete total reads and the input word's tag bit.
  The size header is read after the store. CopyPost records the original source
  word at the destination, exact memory, both possible PCs, updated registers,
  and the segment kernel's register/output frame.
- `Vsa/Sim/ChainMemory.lean:evalBlocks_low` lifts the existing per-block store
  policy to chains. `CopyPost.code` combines it with generated, chunked code
  transport to preserve the mopup image. No extra code-separation assumption.
  `experiments/syi/gen_code_lemmas.py` exposes optional transport certificates;
  default output for its other consumers remains unchanged.
- `segmentPost_of_block` shares the adapter from complete block results to the
  reflected post interface. Targeted capped builds pass. The preceding enqueue
  and grey-payload increment landed as `3970479` through scripts/integrate.sh.
- Next: fold field progress with the loop rule and compose pointer oldify calls.
  This is one immediate-valued iteration, not the full mopup or G2 theorem.

## Concrete enqueue and grey payload (2026-10-03)

- `EnqueueAccess.lean:enqueue_machine` discharges the real allocation-return
  path's scalar loads, stores and unsigned size branch. Its inputs are
  platform/code/register pins, RAM geometry, the old queue view and write
  separation. Both load byte lists are total reads of memory after the
  preceding stores. The original first-field read follows from separation
  already needed to preserve the caller root; no additional alias premise.
- `EnqueueRunPost` retains the segment kernel's register/output frame for
  later epilogue composition and proves the copied first word equals the
  original source word. Allocation execution and freshness remain open.
- `PendingPayload.lean:pendingPayload_enqueue` establishes the typed grey
  payload assertion using Eqv.list/Eqv.val and Eqv.transport: first field at
  the copy, remaining fields at the source, all under the original placement.
  Its source-suffix footprint supplier remains explicit. The intrusive next
  link in the copy's second word is never treated as a payload value.
- Targeted capped builds pass. The prior six-store effect landed as `7d04d6a`
  via scripts/integrate.sh, exit 0. Next: scanning/blackening invariants and
  oldify/mopup call composition; G2, live-word Fits and compiler safety are open.

## Allocation-return enqueue effect (2026-10-03)

- `Generated/Enqueue.lean:writes` proves all six stores on the real
  multi-field allocation-return route: caller root, zero source header,
  source forwarding pointer, copied first field, global head and next-source
  link. `run` composes the two generated blocks through the queue insertion
  jump, stopping at the native epilogue.
- `QueueEnqueue.lean:enqueue` turns that effect into the new queue view,
  caller-root update and copied first field. Existing links use the shared
  `WorkQueue.body_frame_log` and Eqv.transport. The scalar load identifying
  the prior queue head and finite write separation remain named premises;
  allocation freshness and the concrete access supplier are still open.
- `Readback.lean:word_writeLog_at` reuses the existing indexed write-log
  read64 theorem and total-read bridge. No byte arithmetic or instruction
  execution is re-proved. Targeted capped Enqueue/QueueEnqueue builds pass.
- The fully supplied queue-pop increment landed as `1c9fd67`, full gate exit 0.
  Next: enqueue access/load suppliers and partial copied-field invariant;
  allocator/call splicing, full G2 and production Fits remain open.

## Concrete intrusive queue pop (2026-10-03)

- `QueueAccess.lean:pop_machine` discharges the generated SegPre from
  platform/register pins, the generated code image, three node RAM windows,
  a nonzero source address, and the concrete queue view. Its first-field
  branch is computed from the actual loaded word; no branch/run/next-load
  premise remains. The global write window is checked from Layout.
- `Queue.lean:WorkQueue.pop_loaded` proves the ghost head is removed while
  every disjoint tail link survives. `PendingCopy.eqv` uses raw-word Eqv
  cells for the zero source header, forwarding target and next SOURCE link;
  `body_frame` uses Eqv.transport and existing write-log frame lemmas.
  Queue addresses are 64-bit machine words, so pointer arithmetic agrees
  directly with generated loads. This link view does not claim copied-field
  correctness, allocator ownership or termination.
- `ChainPlan.lean:chainPlan_facts` separates reusable code certificates from
  finite scalar-access and branch certificates. The generator now supplies
  MopupPop.code_facts for both outcomes, using ELF pins and decode theorems.
- Targeted capped builds pass; all new declarations are in OCaml/Audit.lean.
  The law checker again passes 2000 cyclic/aliased intrusive-queue cases
  and the existing Forward/Infix/remembered-set/promotion checks.
- Previous entry/pop effects landed through the full gate as `f21deba`.
  Next: copied-field partial-relocation invariant and oldify call splicing.
  Full mopup/collection, production live-word Fits, and compiler GcSafe remain open.

## Mopup queue entry and pop (2026-10-02)

- `Generated/MopupControl.lean:entry_registers` proves the actual prologue
  establishes the todo-list, Caml_state and ephemeron-sentinel registers,
  plus the two loop constants. Every data symbol comes from generated Layout.
- `Generated/MopupPop.lean:run` composes the nonempty-head path through the
  first-field branch. `queue_write` and `Post.todo` prove its single store
  replaces the todo-list head with the next-source pointer loaded from the
  copied block. Both immediate and pointer first-field branches are checked.
  The concrete load/branch/platform SegPre and ghost queue preservation remain
  obligations; this is not yet a whole-loop or collection theorem.
- `Vsa/Sim/SegmentSummary.lean:segmentSummary` shares the named reflected
  postcondition and FnSummary adapter for composed generated routes; the
  existing immediate route now reuses it.
- Layout's target-compiler measurements now include minor-collector tables,
  ephemeron element fields, and domain-state collector offsets. The symbol
  generator supplies the todo list and ephemeron sentinel addresses.
- Forward edits cover saved callback accu/env/stack slots and the pending
  exception root introduced on main; these use the same directed-edit law.
- Targeted capped builds of GcSafe, Layout, LazyForce, Immediate, MopupControl
  and MopupPop pass. Earlier segment coverage landed as `b638f22` through
  scripts/integrate.sh. Next: supply the queue invariant and concrete load
  witnesses, then compose oldify calls. G2 and production Fits remain open.

## Round 2: GC-safety (2026-10-02)

Kiran chose option (a): a `GcSafe` precondition beside `Good` and `Fits`;
`BcSem` stays deterministic. The earlier decision request is resolved.
`OCaml/Bytecode/GcSafe.lean` defines contextual Forward edits/equivalence,
collection-closed reachability through directed shortcuts (never inverse
reboxing), conservative collection boundaries, and
halting/output/divergence equivalence of continuations. The safety premise
is threaded through Layer A and end-to-end statements; their targeted
build passes. The concrete boundary classifier remains a machine obligation.

The proposed general argument from typing is false: a well-typed program
using only Lazy.force, Lazy.from_val, physical equality and Gc.minor prints
`false true`. See `c/tests/gc/lazy_physical_equality.ml` and
`scripts/check_gc_safety.py`. Thus GcSafe must be established for each
program; neither typing nor the local force-path proof establishes it.

Host validation of the pinned boot/ocamlc compiling hello.ml gives identical
stdout, stderr and .cmo under default, 4096-, 8192- and 16384-word minor
heaps; instrumented counts are 1, 61, 32 and 17 minor collections.
`results/gc-safety.json` records hashes and the static scan's 5741 potential
observation sites. All sites conservatively remain potentially lazy-reachable:
this scan does not discharge type/alias/control-flow obligations.
`GcSafe boot/ocamlc` remains OPEN.

The real CamlinternalLazy.force bytes are extracted via runbc --lean by
`scripts/gen_lazy_force.py`. `force_forward` and `force_value` prove the already-forced paths in
twelve and fourteen real BcSem steps. `force_observations` proves identical
continuation halt/output/divergence; `force_argument_edit` exhibits their
forwarding edit, and `force_integer_observations` discharges the primitive
precondition for integer payloads. The generic value theorem explicitly
requires a successful tag read with non-Forward/non-Lazy result. Its tag read and non-float-array payload read do not allocate;
forwarding between a cached tag test and its payload read is not a runtime
collection boundary. The bytecode semantics has not been changed.

The host/BcSem force regression agrees (1145 steps, exit 0). The generated
bytecode is pinned by `scripts/gen_lazy_force.py --check`; the full gate
checks both extraction and regression. `Run.halts_after_iter` and
`Run.div_after_iter` supply the different-length continuation reasoning.
`Gc.ObservedAt.collect` composes a named `CollectionEffect` with GcSafe;
its actual oldify/mopup machine run and post-representation remain open.
`Theorems.boot_ocamlc_gcSafe_Statement` names the compiler obligation.

## Immediate-value oldify composition

- Round 2 landed with full gates: `025786c` (GcSafe interface/compiler
  validation) and `98f4e0b` (real force proof/observational composition).
- `Gc.Generated.Immediate.run` composes the two generated machine segments
  from oldify entry through the immediate-value return. `Post.root_value`
  proves the final root contains the unchanged word. `stack_restored` checks
  the prologue/epilogue arithmetic; `Post.returns` identifies the caller target
  under its explicit saved-word readback premise. The exact write log and
  register outcome remain available. No caller supplies a machine run.
- Its `SegPre` still requires concrete code, branch, load/store and platform
  facts. A LoopHead-to-SegPre supplier, heap-pointer paths, recursive call
  splicing and the mopup invariant remain open. This is one route, not G2.
- CollectionPoint includes APPLY/APPTERM and POPTRAP, whose interp.c paths
  enter pending-action processing as well as explicit CHECK_SIGNALS.

## Mopup regions and unsigned comparison

- `gen_fn.py --region-exits` preserves both branch arms and cuts only at
  explicit control boundaries. Limits remain 150 instructions/20 branches
  per region; region extraction supplies neither loop invariants nor calls.
- `gen_gc_rows.py` partitions all 149 mopup instructions without overlap or
  gaps: Entry 19 instructions/0 branches, Deferred 41/10, Ephemerons 89/19.
  `results/gc-mopup-regions.json` records the boundaries and counts. Every
  region, code pin and row is generated and included in the audit.
- The first ephemeron-row check exposed unsupported SLTU in the reflected
  decoder. `CompareAlu.execute_compare_char` factors the existing signed and
  unsigned Sail equations; the existing MKind.slt constructor now takes an
  unsigned flag defaulting to false. BlockMem/BlockTerm reuse the same
  comparison proof and retain their existing budgets. Modified copied files
  were removed from the discipline grandfather list; discipline passes.
- The capped generated-audit build now passes with all mopup regions.
  Deferred-list and ephemeron invariants, oldify call splicing, and the
  complete CollectionEffect are still open. The next composition step is
  the deferred-work body and its intrusive queue/partial-relocation invariant.

## Status

G2 remains open. `Fits` still measures total allocated words; no claim that
the one-line ocamlc run is covered by G2.

Latest targeted build: LazyForce, Gc.Observed and Theorems passed. The axiom
audit passes with only propext/Classical.choice/Quot.sound. Landing uses the
full integration gate.

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
  one-line compiler Layer A budget theorem. The Forward decision is resolved by GcSafe; machine execution and
  reclamation gaps remain explicit.


## Fixed-address .embed migration preparation

- Foreman notice received: .text entry addresses stay fixed, but data symbols
  and gp/auipc-relative instruction immediates move. Concrete data references
  in this lane use `OCaml/Vm/Layout.lean`; no hard-coded ELF data address was
  found. Numerical addresses in the Forward counterexample are synthetic
  witness addresses, not runtime symbols.
- `scripts/gc_cfg.py` now records the pinned ELF SHA-256 and the exact
  little-endian instruction SHA-256 for each collector function. CFG-only
  comparison could miss changed immediates with unchanged control flow.
- The fixed-address .embed migration is on main. This worktree rebased on
  its regenerated Layout/decode/code pins; `gen_gc_rows.py --check` and
  `gc_cfg.py --check` pass on the migrated image.
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
- The generated audit enumerates all row, segment, composed-route and
  code-pin declarations, including the new mopup regions. The capped build of `OCaml.Vm.Gc.Generated.Audit` passes,
  and a separate capped Lean audit exits 0 with exactly those declarations
  and only the three permitted standard axioms.
- Reproduce the bundle with `python3 scripts/gen_gc_rows.py` and check
  with `--check`. The strengthened postconditions pass the capped build
  (554 jobs). The full gate imports the generated audit and checks both
  row/code generation and CFG fingerprints on the migrated image.
- Landed `ae39c98` (promotion footprint) and `2615273` (generated machine
  segments) through scripts/integrate.sh, exit 0. The final gate audits
  779 theorems, including all 387 generated collector declarations;
  generated-file checks, code-pin checks and abstraction gate pass.
- G2 is still open: GcSafe resolves the Forward specification choice;
  remaining obligations include allocator/call summaries, concrete roots/table
  linkage, the partial-relocation loop invariant, and major reclamation.
  Neither production Fits nor the one-line ocamlc budget claim is changed.
- Concrete data addresses continue to come from Layout; instruction words
  and code addresses come from the pinned ELF/decode generators.
