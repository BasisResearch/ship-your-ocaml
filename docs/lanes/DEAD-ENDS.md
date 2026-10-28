# Routes not to repeat

- 2026-10-28 CODE epilogue elaboration (checked build obstruction):
  the combined `0x80004c64`–`0x80004c98` reload/restore summary hit the
  default 200,000-heartbeat whnf limit. Do not increase that limit or
  recursion budgets. The generator now exposes `SeekOptionalReload`,
  `SeekOptionalRestoreBank` and `SeekOptionalRestoreLink` as bounded
  observations of the same native instructions, for FnSummary composition.
  The reload slice needs its own declaration prefix because it shares the
  full epilogue's entry address. Existing source/length/offset certificates
  stay unchanged. For ADDIW, expose the actual `extractLsb (count + sext imm)`
  expression (`seekCountDown`), and use the existing store/skip adapters
  when a load follows its region's own saves. The combined
  entry also exceeded kernel recursion at default limits;
  `SeekOptionalAdjust`/`SeekOptionalSave` separate its stack adjustment
  from the three saves and count load. These bounded summaries check
  without changing any elaboration budget.

- 2026-10-28 CODE four-byte strncmp ingress (interface inspection):
  `strncmp_dispatch` is an unaligned-pointer summary; it cannot be applied
  unconditionally to the CODE call. The executable literal is at the
  8-aligned address `0x80055e60`, and no unaligned selected-table premise is
  supplied by reset. With count exactly four, the aligned route instead
  takes `strncmpX0cc8FSeg`, `strncmpX0cccFSeg`, `strncmpX0cd8TSeg` to the
  existing byte loop, without loading a word. `strncmp_four_dispatch`
  handles both alignment alternatives. Keep the CRCS equal first byte and
  actual second-byte mismatch; neither an unaligned assumption nor a
  stock-image word certificate supplies this native call.

- 2026-10-28 counted unary classification: `first` around
  `exact Or.inr (by simp)` selected the unfinished name-disjunction proof
  for the eight wrong-arity names and exit, leaving `False` goals before
  trying the actual semantic rejection (`/tmp/counted-unary-first.log`).
  Use goal-closing `solve` branches with `apply Or.inl; decide` and
  `apply Or.inr; simp`, then the existing exit exclusion and concrete
  `primF1Impl` reduction. This is a tactic-selection failure; no semantic
  obstruction or additional supplier is claimed.

- 2026-10-28 actual opening runtime reconstruction:
  blanket equality on the original keptFootprint is false for opening:
  caml_all_opened_channels changes to the fresh record. Adding that head to ignoredStatics and removing it
  from keptFootprint globally also breaks in_channelsHead and
  the ordinary allocation/window/record frames that use it to preserve the
  selected list. Keep the full footprint and its existing transfer API;
  f1_core_except_head instead consumes only core reads outside that word,
  and its heap supplier reconstructs the actual changed list. StaticApart
  now excludes that independently checked head for core static reads.
  OpenedOut alone does not expose the actual OutInput/OutNursery frame;
  after now receives the caller's existing inputs and successful selected
  list bound. Never substitute an arbitrary native stack/nursery frame or
  assume a returned LibHeapAt. spatial_heap now returns named protection
  for the actual fresh record as well, on its same credited returned H/cap.
  recordBytes = 65616 is the full malloc request; chanRecordBytes = 65608
  is the represented record extent. Their equality is refuted by decide.
  Retain the full block in H, and use its checked size inequality for the
  represented named/custom protection; preserve the full spending charge.
  The conservative eight-byte young_ptr exclusion in OpenedOut.kept does
  not frame every byte of the adjacent young_limit word. Use the actual
  OpenedOut.youngLimit readback (as listing does for its limit) and frame
  the remaining core reads; do not demand a stronger arbitrary byte frame.

- 2026-10-28 CODE selected-table provenance (interface inspection; repaired):
  the current `GcTableAt` and final readiness contracts alone did not expose
  the page table's original fresh-allocation separation from the selected
  descriptor/name blocks. Do not reconstruct this from an arbitrary later
  heap or snapshot. `GcTableSource.fresh` now retains the actual allocation
  over the original source ledger; `ResetInitStack.sourceTableFresh` carries
  it to the atom call. The filename's original `OpenOcamlrun.apart` ledger
  also includes the temporary search copy before the domain/ref-table
  ledger: its membership proof must include that real prefix. Selected
  LiveFrames and native scratch-bounded source frames now close these
  current-source obligations; the reverse scan remains separate.

- 2026-10-28 selected credit repair:
  the old advertised-capacity obstruction does not refute the strengthened
  runtime. `LibHeapAt.credit` now requires ordinary reserve plus the actual
  `customTableReserve`; its startup and real frame producers retain that
  field. `LibHeapAt.tightCapacity` explicitly returns only the old HeapReady
  numeric projection, and `customCredit_obstruction` states the old ordinary
  numeric room premise. `CustomMemInput.zeroCapacity` still concerns only
  the uncredited leaf input; the accepted native call separately consumes
  credit. `CustomMemReturned.heap_zero` forgets the credited native return.
  None supplies a counterexample to `CustomMemCountedReturned.credited` or
  the repaired listing runtime. Never attach a spending law to the unrelated
  forgetful return witness: the listing and opening callers select the
  ledger/capacity inside `credited`, then retain it through actual frames.
  Register-only reserve transport should use `customTableReserve_of_mem`
  and `customTableReserve_congr`; broad simplification of Config-indexed
  observations produced apparently identical but mismatched types. The
  bounded scalar observations check at default limits.

- 2026-10-28 concrete custom physical/context production:
  occupancy is still only a component. `CustomPhysical` records both exact
  resource target words, all seven zero/allocated table observations and
  footprint caller separation; `CustomContext` separately pins the native
  ratios, max size, heap sizes, lambda, Caml_state and table identity.
  Source/interface inspection rules out treating table shape without caller
  separation as enough for the global `CustomMemCall.apart`/`physical` laws:
  arbitrary backing addresses need not be below the native stack or outside
  caller regions. `PhysicalState` filters the existing footprint by a full
  physical witness; startup and its actual frame now produce separation.
  This is an interface requirement, not a claimed reachable counterexample.
  The older `outW_openWindows` helper admits only the static resource band;
  it cannot establish read-only ratio/lambda/Caml_state frames. Use existing
  `outW_openWindows_static` with the concrete errno/head certificates, and
  normalize record-size addition before read-window transport. Inferring
  positivity with `omega` over the large opening context hit default
  recursion; compose selected `block_bounds.1` with `Covered`'s lower bound
  via `Nat.le_trans`, without unfolding 64 KiB sizes or raising limits.
  The actual minor denominator is **2097100**, not 2097152: native custom.c
  divides nursery bytes by 100 before multiplying by the ratio. The ground
  parameter and finite rounding-target checks do not prove native
  `__floatundidf`/`__divdf3`/`__adddf3`/`__gedf2` execution or its threshold
  branches. That precise linkage remains in `CustomMemCall`; spending on the
  actual selected returned capacity remains `CustomMemSpending`'s native
  supplier. See `CUSTOM-READS.md` for the source/disassembly read set.

- 2026-10-28 CODE seek source selection: the pinned runtime ELF's stock
  `.embed` contains CODE length 11836. The selected `WhileMinImage` loader
  pieces contain CODE length 764, file length 9388, and seven descriptors.
  Reading the stock ELF payload gives the wrong scan and fd position for
  this reset theorem. Native instructions and the literal CODE pointer still
  come from the pinned ELF; file observations must use the actual reset's
  initial source image. `SeekSectionData` checks those bounded loader reads,
  not a captured execution or a current-memory frame.

- 2026-10-28 CODE scan comparison: assuming every non-CODE descriptor differs
  in its first byte fails on CRCS. The generator's first-byte-only guard
  rejected the actual table; `seek_crcs_common_prefix` now checks equality
  at byte zero and inequality at byte one. Use the existing bounded strncmp
  path for this prefix, with comparison count exactly four.

- 2026-10-28 CODE source frames (interface inspection): `InitGcDone.low`
  requires `x < heapStart`; it cannot transport owned descriptor bytes or
  the embedded file image. `MinorHeapSet.lowKept` and `MajorHeapInit.lowKept`
  have the same low-address restriction, and their caller frames start
  above the embedded image. The bounded caller component is now proved
  through GC/stack/atom/root/interpreter execution and supplies the current
  trailer pointer/count. It does not supply the descriptor, OpenFile,
  embedded source or fd-position observations. Preserve these through
  selected LiveFrame/static/domain windows and actual heap-ledger inclusion
  before composing reset with the reverse scan. Steps alone supplies no
  such memory frame. This is a contract gap, not an impossibility theorem.

- 2026-10-28 listing interface repair (checked):
  `VmPoint.arbitrary_stack` and `unrestricted_entry_obstruction` in
  `Sim/OutListObstruction.lean` check the old entry defect at
  `sp = heapEnd + 16`, conditional on an input runtime/geometry witness.
  This is not a reachable counterexample or global inconsistency. The
  replacement takes the actual `CcallSetupPost` and stack room;
  `f1_outList_entry` derives the full selected ledger and payload separation.
  Never restore the independent-sp interface or an arbitrary-H allocator
  write law as a runtime supplier.

- 2026-10-28 native custom capacity (checked interface obstructions):
  `CustomMemInput.zeroCapacity` retains every native precondition while
  advertising zero; `CustomMemInput.credit_obstruction` refutes deriving a
  positive charge from that contract. `LibHeapAt.tightCapacity` originally kept the old
  selected spatial invariant at exactly its ordinary reserve, and
  `LibHeapAt.customCredit_obstruction` refuted deriving additional custom
  credit there when the table is empty. After the selected credit repair,
  those lemmas explicitly state the old HeapReady/numeric projection; they
  do not assert the strengthened LibHeapAt at the tight capacity. The actual
  returned heap also admits a zero-capacity witness
  (`CustomMemReturned.heap_zero`). These do not show a physical shortage,
  nor refute existence of a better returned capacity witness. Neither
  ownership nor `HeapReady` alone proves future `LibHeapAt.room` after
  native table spending. Carry separate input credit, actual table shape,
  and spending on the same returned ledger/capacity. `CustomMemSpending`
  names the native component of the accepted `CustomMemCall` obligation.
  The selected-credit repair incorporates it into that named boundary and
  carries it through actual counted listing callers; native execution remains
  named. See the current credit repair entry above.

- 2026-10-28 listing default kernel recursion: the represented channel
  upper bound is `(b + chanOffBuff) + ioBufferSize`, whereas the selected
  record helper takes `b + chanRecordBytes`. Relying on definitional equality
  unrolls the 64 KiB addition and fails kernel recursion even after factoring
  the union's cases (`/tmp/outlist-f1-entry2.log` through `entry12.log`).
  Normalize explicitly with `simpa only [chanRecordBytes, Nat.add_assoc]`.
  The entry then checks at default limits (`/tmp/outlist-f1-entry13.log`).
  No budget increase is needed. The actual returned young-limit word must
  be used separately: the synthetic listing footprint includes its store,
  even though the checked native return restores the same value.

- 2026-10-28 original-wrapper carved-header window: `EntryLargeSource`
  gives a lower heap bound and a nonwrapping extent below `2^64`. It does
  not imply the carved header's ordinary-RAM upper bound (`2^32`), upper
  major-arena membership, or selected-ledger ownership. This is interface
  inspection, not a reachable-state counterexample. `AllocEntryLarge.Facts`
  consumes `sourceUpper : sourceEnd c ≤ DlHeap.heapEnd` explicitly and derives
  the carved `WriteWindow` from that bound and the source header alignment.
  It does not infer ownership. Native separation must cover both the
  wrapper's 48-byte frame and the free-list's 32-byte frame, including the
  saved tag. Natural allocated/free counters also retain independent
  original nonoverflow/nonunderflow credit; representation supplies neither.

- 2026-10-28 original-entry least-large routing: absence of suitable small
  classes does **not** supply the native zero-filtered-bitmap branch from
  the current `SmallRepresentation`. `MapConsistent` constrains only bits
  0–15, whereas the generated SLLW/AND mask also retains bits 16–31 (and
  the signed LW may extend bit 31). `BestFitEntryLarge.lean` now checks
  `highBitmapMemory_obstruction`: a concrete total memory with all small
  slots zero and bitmap `0x10000` has full `SmallRepresentation` of the
  empty family; positive request 1 still filters to `0x10000`.
  `no_representation_only_zero_bitmap` formally refutes that supplier.
  This is an entry-interface counterexample, not a native reachable-state
  counterexample. Empty lists are only the refuting witness, not a routing
  precondition; `EntryInput.missing_of_noSuitable` still permits lower lists.
  Do not replace the filter by a sixteen-bit filter, assume every list is
  empty, or add a zero-bitmap premise and call it a producer. Continuing
  requires a stronger bitmap invariant with unused bits zero, preserved by
  the real exact/next-size writes; its native/caller production stays open.
  The obstruction remains valid for the old predicate. The separate bounded
  refinement now repairs this interface: `BoundedBitmap.high_iff` excludes
  high bits, and `filtered_of_noSuitable` proves the actual native zero
  filter. `BestFitEntryLargeReturn.allocate_entry_large` now derives the
  original source/stack setup and returns the physical split facts by reusing
  unchanged `allocate_large`. Its natural counter theorem keeps explicit
  credit. Neither the zero-map captured-memory certificate nor the pure
  singleton observation is a native initialization/caller producer. There is
  no new runtime obstruction; checked build/audit evidence is in `a6-gc.md`.

- 2026-10-28 counted fresh-id/exit boundaries: stack-window count framing
  does not cover `counterWindows`, whose actual store is the low static
  `oo_last_id` word. This is interface inspection, not a reachable-state
  counterexample. Use the original counted opened-list witness to align the
  selected `LibHeapAt` channel records, its malloc block bounds and
  `CustomMemCall.owned` from that same ledger. Static custom bytes are only
  the existing resource word; dynamic custom bytes belong to selected live
  blocks. `accounting.frame` then preserves physical counts and
  `ChannelCountFrame.of_frame` preserves refs/links. Ordinary runtime facts
  alone still supply no count witness. Return counts use unchanged semantic
  channels and `ChannelCustomsRepr.at_geometry` at the actual returned cp.
  `prim_caml_sys_exit_returns` proves only that `.ok` is impossible; using
  it as a halt execution would omit dispatch, setup and the native exit.
  Project `CountedLoopAt.toLoopAt` and reuse `ccall1Exit_pinned`; its checked
  `caml_sys_exit_halts` already handles the integer argument, OS-result
  split, status and console. There is no counted successor to construct.
  The checked `counted_c_call1_row_of_next` composes that halt branch using
  `ArmOutcome.of_cases`; complete success coverage remains a separate input.
  Fresh-id model `simp_all` alone left the updated-world channel projection
  unresolved (`/tmp/counted-fresh-exit-rows2.log`): simplification exposes the
  three actual return equations as a conjunction. Destructure those equations
  explicitly, then use the unchanged channel projection. This elaboration
  failure needs neither a new semantic premise nor a larger proof budget.

- 2026-10-28 counted console transport: whole `world.chans` equality is
  not a semantic frame for successful flush/output. The real implementations
  set the selected channel's buffer and/or offset; a whole-record memory
  frame likewise excludes their actual writes. This is direct model/contract
  inspection, not a reachable-state impossibility claim. Use the checked
  `ChannelRefsSame` (length and per-id refs), derived from successful
  `flushChan`/`putChar`/`putBlock`, and `ChannelCustomsRepr.of_refs_same`.
  A total-count equation alone cannot recover per-record observations or
  physical accounting. The native frame observes refcount/next words through
  actual `consoleWindows`, selected `LibHeapAt` bounds/disjointness and
  custom-space separation. Recover the actual returned placement using
  `ChannelCustomsRepr.at_geometry`; never assume it matches the entry place.
  In the recursive model proof, leaving the intermediate updated record as
  `_` lets Lean infer the original record from the refs projection before
  it sees the recursive tail. Give the real buffer/offset update explicitly
  to `ChannelRefsSame.set_after`; no stronger semantic or runtime premise is
  needed. Checked in `ConsoleCounts` and the complete `CountedConsoleRows`.

- 2026-10-28 exact-size representation readback: mixing slot readback,
  scalar address rewriting and represented-family transport in one theorem
  exhausted the default heartbeats at the head-store seam
  (`/tmp/a6-exact-preserve.log`). This is an elaboration failure, not a native
  obstruction. Factor `BestFitExact.effect_parts`, `effect_head`,
  `effect_bitmap` and the static `BfShape.exact_effect_head` first; consume
  those scalar observations before `SmallShape.pop` and header/map transport.
  The bounded proof checks at unchanged limits. The actual accounting cell
  is below the small-list slots, so its readback separation uses
  `counter + 8 ≤ slot`, not the opposite interval order.
  `SmallRepresentation` has no relationship between the modular counter and
  the natural sum of free extents. Keep actual sufficient credit separate
  in `BestFitExact.Post.counter_nat`; do not infer it from list preservation.

- 2026-10-28 lead listing-supplier inspection (not yet a checked obstruction):
  `OutListRuntime.entry` quantifies over `sp` but receives only runtime and
  `LoopGeometry ... high`, which does not index that stack pointer. Its
  `VmPoint` includes `[sp - 16, sp + 8 * stack.length)` while its output
  requires every point below heapEnd. Taking sp = heapEnd + 16 exposes the
  missing actual stack/setup hypothesis even when the semantic stack is empty.
  Prove the conditional interface obstruction before claiming impossibility;
  no reachable-state counterexample or global inconsistency is established.
  `OutListRuntime.runtime` also quantifies over arbitrary H and memory writes
  in `vsaFoot H`, without selected input/returned heap evidence. Such byte
  framing cannot supply allocator validity by itself. Use the actual native
  post's selected heap, ledgers and frames, not unrestricted allocator writes.
  Finally `CustomMemReturned.heap` returns an existential capacity with no
  spending bound; `LibHeapAt.room` reserves future C allocations. Selected
  ownership/spatial preservation alone does not establish this reserve.
  Any repair must track a concrete custom-table allocation charge/reserve at
  the accepted named native boundary and its actual callers, rather than
  assume whole-primitive runtime or an arbitrary returned LibHeapAt.

- 2026-10-28 counted C_CALL3/5: a successful-return arity contract alone
  does not exclude `.exit`/halt. The checked `primF1Impl_exit` interface
  identifies `caml_sys_exit` and its unary length; the shared
  `primF1Impl_wrong_arity` proof instead classifies every implementation
  pattern and proves the entire result is `.unsupported` outside 1/2/4.
  Also, `stack.take k` has length k only after the real stepI depth check;
  apply it after the combined negative-index/short-stack guard, retaining
  malformed-operand and absent-slot rejection. Do not infer primitive
  arities solely from names or constrain the table/GoodF1.
  A stronger candidate claiming `.unsupported` for every operand is
  refuted by the actual `opt none = .wrong` branch for an absent primitive
  slot. Preserve `.wrong` there; the shared rejection theorem covers both
  error constructors and selected wrong-arity F1 primitives stay unsupported.
  In the shared operand helper, `split` after `rw [semantics]` can split
  the compiler's singleton-list match even after `rcases args`, yielding
  no stack-depth evidence. First `change` the singleton goal to the actual
  combined conditional, then split that guard; otherwise the length proof
  correctly fails on a short stack.

- 2026-10-28 counted ordinary return adapter: the loop-entry interface gap
  recorded below is resolved by an explicit `ChannelCustomsRepr` argument to
  `CountedPrimReturnsAtR`, supplied by `CcallReady.of_counted_loop`.
  `CcallReady.retarget` lifts original readiness with that witness;
  `CountedCcallSetupPost.local` separately uses the actual callee-entry
  counts. No backward physical-count transport or count inference from
  ordinary runtime facts is valid. Return transport uses unchanged model
  channels and `ChannelCustomsRepr.at_geometry` at the actual returned cp.
- 2026-10-28 counted C_CALL2 elaboration: its native bytecode guard is the
  combined disjunction `index < 0 ∨ stack.length < 1`; simplifying as two
  nested conditionals leaves `if False ∨ False`. Reduce the actual combined
  guard (`or_self` after both facts), and project `ready.stackFits` explicitly
  before `stack_space`/`omega` supplies the argument-read window. Both routes
  now check without changing guards or budgets.
- 2026-10-28 primitive model certificates: `simp only [primF1Impl]` leaves
  string-name dispatch tests unresolved; blindly splitting that result
  explores unrelated opening/listing branches, with failed dependent
  elimination and invalid arity goals. Reduce the concrete name using
  `simp [primF1Impl]` before splitting its remaining semantic options. All
  nineteen arity/channel certificates then check at the existing limits.
- 2026-10-28 NULL-interpreter saving region: packaging all thirteen stores
  in a single startup `BlockInput`/`registers_of_blocks'` proof reaches the
  kernel's default recursion limit even after the generated instruction
  normalizations remove symbolic address checks. This is a checked
  elaboration failure (`/tmp/interpreter-init-steps-6.log`), not a native
  obstruction. Split the ELF region at `0x80001e14` (six then seven stores),
  compose their summaries and logs, and keep the default proof limits.
  The mixed frame-adjustment/six-store prefix also hits that limit
  (`/tmp/interpreter-init-steps-7.log`); keep the generated `addi sp,-528`
  region separate at `0x80001dfc` from both store-only regions.

- 2026-10-28 interpreter initialization / descriptor ancestry: the old
  `ResetInitStack` retained reset identity and a global run but discarded its
  actual `ResetReadSections` witness. The subsequent atom/backtrace interfaces
  therefore could not supply descriptor/fd/argv provenance for later CODE
  loading. This is interface inspection, not a reachable-state counterexample.
  The real GC-call producer now returns `ResetGcCalled` with local `Steps`;
  its old existential API is a projection. Stack, atom and backtrace producers
  retain their source witnesses and local runs. Do not add arbitrary facts
  about the original state to the initialization input or infer a memory
  frame from `Steps` alone. Earlier descriptor/file/argv memory frames still
  need the actual GC/stack/atom/root-store effects.

- 2026-10-28 interpreter initialization / entry route: `entry_save` requires
  a nonzero program argument and takes the branch to `0x80001e38`. The real
  startup call sets both arguments to zero, falls through `0x80001e34` to
  the unit block at `0x800035e0`, then uses `interp_return` at `0x8000331c`.
  Do not instantiate the nonzero theorem or assume threaded-code setup in
  this ELF. The two bounded interpreter regions are generated from the ELF
  by `gen_startup_rows.py` through `gen_fn`; no captured execution supplies them.

- 2026-10-28 counted growth capacity frame: using one implicit capacity for
  both entry `LibHeapAt H cap` and returned `GrowDone H capacity` forces the
  real call's `cap - tableCharge` to unify with cap. Lean then unfolds the
  large subtraction through Nat.rec and hits default recursion limits. Keep
  caller and remaining capacities separate in observation-only frame helpers;
  `BarrierGrowRuntime.afterGrow` retains the actual `cap - tableCharge` native
  post and `f1_afterGrow` retains the real spending relation. Do not increase
  budgets or erase the allocator's capacity change to hide this mismatch.

- 2026-10-28 counted barrier insertion: shared ownership is insufficient to
  separate dynamic remembered-set storage from custom storage.
  `LibHeapAt.custom` covers custom storage in the selected H, while
  `RefStorage.covered` may cover the same range; `apartCustom` separates only
  the fixed custom-table struct. `RefStorage.custom_alias` checks that those
  interfaces retain `CustomLedger` under aliased addressing observations
  while `RefCustomApart` is false (a conditional interface obstruction). It does not assert an alias in reachable states
  or refute the complete `f1Runtime`. `f1_afterGrow_customApart` instead derives
  separation for the actual first-allocation return from `GrowDone.disjoint`
  and selected `CustomLedger.owned`. A supplier at every runtime state needs
  an invariant and real preservation/startup/custom-call producers. Do not
  infer it from two Covered witnesses or add it silently to GoodF1.
  Resolved for the selected invariant by `LibHeapAt.refCustomApart` and
  `f1_refCustomApart`: `CustomSpace.allocated` protects the real nonzero
  remembered extent in `namedBlocked`; arena bounds separate the static
  resource and `apartBlocks` separates the domain resource. The weak-interface
  alias obstruction remains valid; it does not include `CustomSpace`.

- 2026-10-28 counted full-table growth: `BarrierGrowthFull f1Layout` returns
  only the base runtime. It cannot be treated as
  `BarrierGrowthFull (countedLayout f1Layout Customs cp world)`: the latter's
  BarrierDone must also retain physical Customs, natural channel refcounts
  and opened-list links at that frozen placement/world, together with every
  ordinary native/runtime field. G2 must supply this stronger existing
  obligation for each cp/world, or expose real low-level effects from which
  its extra count frame can be derived. The unallocated branch uses the
  actual GrowDone.kept/disjoint and does not need that full-table premise.

- 2026-10-28 custom read-context inspection: native `caml_alloc_custom_mem`
  reads ratio/max-size globals, domain heap sizes and memprof state beyond
  the current mutable custom footprint (`custom.c`, `memory.c`). Its input
  currently contains leaf/heap/register/frame/nursery facts, while the global
  readiness frame preserves only state bytes and Caml_state. Do not infer
  those external runtime observations from physical count/ownership or the
  rational quiet-bound inequality. Audit and supply concrete stable call
  pins at actual native boundaries; `sol-custom-physical-runtime.md` queues
  this work. This is source/interface inspection, not a checked machine
  counterexample or global inconsistency claim.

- 2026-10-28 counted division channel semantics: fully splitting the unfolded
  DIVINT/MODINT effect before applying the shared `raiseTo` channel lemma
  expands its dependent trap-frame match and fails dependent elimination.
  Apply the named semantic-operation helpers before each further split;
  retain the actual caught-raise native row through `counted_raiseRuntimeFrame`.
  The aggregate 149-opcode filter count also exceeds elaborator recursion
  under plain `decide`; use kernel evaluation of that generated literal census,
  without changing proof budgets or count/frame premises.


- 2026-10-28 custom global-frame review: the candidate is now checked by
  `Gc.global_records_frame_obstruction` in `CustomFrameObstruction.lean`.
  Its minimal `CustomOutsideFrame` uses only footprint-local apart and frame
  laws. Given `Ready k c`, the pinned valid domain D and retained byte at
  `D + off_extra_heap_resources_minor`, the actual two-entry write log puts
  `D + 96` in the opened-list head and zero at that address plus `chanOffNext`.
  `CallerApart.static/domainField` separate both writes from custom state;
  `Caml_state` is preserved. The framed state then contradicts the rejected
  `GlobalRecordApart` on the constructed singleton list. Generated domain
  offsets and actual `writeLog_out`, `bytesT_writeLog_out` and
  `word_writeLog_at` are used. This is a conditional memory-contract
  obstruction, not a Sail execution or global inconsistency: empty
  readiness/state can remain vacuous.
  The former `.named` likewise depended on an external memory table; that
  dependency is reviewed by inspection, with no checked forged-named-table
  counterexample claimed. Both global fields are removed. `CustomSpace`
  lives beside the selected heap/actual records and named snapshot, and its
  frame explicitly retains table addressing words and the named roots.
  `NamedLedger.read_back` proves why every post-frame representation then
  has the same physical footprint. Do not restore a global record/named law
  or infer record ownership from a linked list alone.
  Directly normalizing the concatenated two-store readback hit the default
  whnf budget during this check; `Readback.word_writeLog_at` supplies the
  bounded readback without reducing the nested memory writes. Do not raise
  the proof budget for that route.
  The old `CustomMemReturned.grows` describes all state bytes, including
  resource accumulators. By contract inspection it alone cannot prohibit
  reclassifying an old resource byte as allocated backing storage. The
  actual native boundary now separately requires `allocGrows`, full
  returned `CustomLedger`, and ready-footprint completeness (`physical`).
  These are explicit physical supplier obligations, not checked native
  execution or an assumed whole primitive return.

- 2026-10-27 counted ordinary C_CALL interface inspection: the existing
  `CountedPrimReturnsAtR` accepts only ordinary `CcallReady` at the original
  loop entry. Its later `CountedCcallCallee.summary` receives counts at the
  native callee entry. This does not directly instantiate a local
  `countedLayout` ordinary `PrimReturnsAt` at the original entry: that needs
  the original counted witness. Carry it from `CcallReady.of_counted_loop`
  in an explicit entry argument or named structure. Do not infer it from
  ordinary `runtimeOk` or transport physical counts backwards without a
  proof. This is interface inspection, not a checked counterexample;
  `tasks/sol-counted-ordinary-calls.md` queues the actual adapter.

- 2026-10-27 custom ownership: the universal-ledger route is refuted by
  `Gc.captured_empty_ready` and `captured_custom_bytes_obstruction` in
  `OCaml/Vm/Gc/CustomLedgerObstruction.lean`. The proof reuses
  `WhileMinAllocator.raw_heap`, `heap_transport`, the captured image agreement
  and capacity. `HeapAt.live/exact` constrain only listed extents, so the
  same cut admits `HeapReady [] (2^24)`, making every arena byte `vsaFoot []`.
  `cut_empty_ready` and `cut_custom_bytes_obstruction` specialize this to
  `WhileMin.cut` without a memory premise; neither asserts reset reachability.
  The old `CallerApart.free` therefore excludes the actual domain minor-resource
  byte and custom-table base byte. Ownership must use the caller's selected
  ledger, with real initial/frame/call producers. This does not show global
  inconsistency of `CustomMemCall`: empty readiness/accounting predicates
  can make the call premise vacuous.

- 2026-10-27 counted allocation adapter: the stack-row pattern quantifying
  a row supplier over every `Layout` cannot directly consume allocating rows
  with only `Fits f1Layout.budget P`. Allocation rows use the selected layout's
  own budget (unlike several stack rows' independent budget parameter).
  Restrict the local supplier to `countedLayout f1Layout Customs cp world`,
  whose budget is definitionally the existing F1 budget; produce its frames
  before applying the generic row. Do not assume Fits/capacity for an arbitrary
  strengthened layout. This is an interface inspection, not a reachable
  counterexample or a change to GoodF1.

- 2026-10-27 counted stack rows: unfolding `stepI` while the operand list
  is unconstrained exhausts the default heartbeat budget even for a fixed
  opcode. Splitting only the opcode, or putting those expansions in separate
  per-opcode theorems, does not fix it. The generated channel-model lemmas
  first expose the finite operand-list shapes using `gen_opcodes.nargs`,
  then reduce the real semantic branch. All 58 certificates check at the
  unchanged budget; native execution is still reused from ordinary rows.

- 2026-10-27 next-size search composition: rewriting the entire search
  memory snapshot before the original header/counter observations in
  `search_allocate` exhausts the default heartbeat budget at the counter
  seam. Rewrite those scalar observations first, then transport only the
  split snapshot with `congrArg`; the bounded proof checks at the unchanged
  limits. Do not normalize the nested pick/pop/split write logs to equate
  the two branch-dependent counter expressions.

- 2026-10-28 original-entry empty-slot composition: a bare
  `simp only [BfShape.slot, BitVec.ofNat_toNat]` leaves the address seam at
  `BitVec.setWidth 64 (R 10)`. A `simpa only [SmallList, slot]` bridge then
  rejects the represented `0#64` against the inferred zero at the
  `bytesT ... 8` boundary (`BitVec (8*8)`). These are observed elaboration
  failures, not machine counterexamples. Use `BitVec.setWidth_eq`, expose
  the slot observation with `change ... = 0#64`, rewrite only the slot
  equality and consume `SmallShape.linked` directly. No new slot-read or
  instruction proof is needed.

- 2026-10-27 counted loop entry: custom-table occupancy is a physical count
  component with a checked startup zero, but it is insufficient by itself
  for `CustomMemCall.accounting.ready`. The resource accumulator words and
  the domain's actual custom-table pointer are independent observations.
  Do not instantiate the named machine premise with occupancy alone or
  infer its quietness from represented refcounts. A complete physical
  runtime predicate needs actual startup/frame/call producers for those
  observations. `table_count_resources_unconstrained` in
  `OCaml/Vm/Sim/CountedEntry.lean` now checks that every major-resource word
  is compatible with the same occupancy. This is a kernel-checked contract
  obstruction, not a reachable counterexample.
  In particular, `CallerApart.domainField` currently admits only
  `extra_heap_resources_minor` in the domain portion of `state`; it does
  not admit the `custom_table` pointer. A predicate observing that pointer
  needs an actual identity pin/frame (or an explicitly corrected footprint
  with its producers), not an assumption that the old state frame reads it.

- 2026-10-27 reset identity review: the older
  `reset_init_stack_reset_exists` interface keeps `Steps (fillZero initial) after`
  but drops the `ElfResetReady` witness retained in its nested
  `ResetReadSections` source; atom/backtrace consumers of only that interface
  inherit the loss. This is interface inspection, not a counterexample to
  the constructed execution. `ResetReadSections.reset` now follows the real
  attempt/open/search/shared-table/parameter source; the stronger
  `ResetInitStack` and `ResetAtomTable` producers carry its witness into
  `ResetBacktrace.reset`, with the old existential APIs as projections.
  Do not infer reset from Steps or assume arbitrary initial configs equal:
  `ElfReset.unique` uses equality of deterministic setup results and both
  zero counters. `ElfReset.of_whileMinElf` transports reset only after proving
  equality of loader seeds and entry/HTIF setup metadata.

- 2026-10-27 initialized-string shared readback: leaving the saved-bank
  prefix as an unconstrained `_ ++ [length-store]` inside `change` forces
  memory/log unification into the default heartbeat limit. Name the shared
  `StringCopy.callerLog` and expose its explicit two-save prefix before
  `writeLog_append`/`word_writeLog`. This is an elaboration obstruction,
  not a counterexample to the native allocation route; the factored
  `caller_readback_at` checks at the default budget.

- 2026-10-27: the real `caml_alloc_sprintf` short-result JAL at
  `0x80013f1c` targets `caml_alloc_initialized_string` (`0x8000c284`),
  not the existing `copy_string_machine` entry (`0x8000c254`).
  `Format.AllocSprintfLong.copy_string_target_obstruction` is kernel checked
  against the generated decoded-call target; `copy_string_argument_obstruction`
  also checks that its a0 decimal length cannot be the local-buffer pointer
  expected by copy_string. `short_continuation` executes the real fit,
  argument setup and JAL to initialized-string entry. Generate/compose that
  function's allocator/memcpy/return boundaries; do not substitute a
  copy_string return or primitive summary at this splice. This refutes the
  requested direct splice, not the initialized-string composition route or
  the reachability of the caller. `Format/AllocSprintfNative.lean` now
  composes the initialized-string route through the original native return
  for plain signed decimal under explicit initial runtime/separation facts;
  reachable caller suppliers, general formatting and C_CALL2 remain open.

- 2026-10-21: a `workspace-write` worker cannot reach the user systemd bus
  or write the home integration queue. Launch the entire worker in the 12 GB
  scope and have the lead run integration after review. Keep the sandbox.

- 2026-10-21: `ulimit -v 12582912` prevents Lean thread/import initialization
  in large closures, even at low RSS and with two threads. Use the actual
  aggregate `MemoryMax=12G` cgroup cap without a virtual-address limit.
- `OpenOutRuntime.budget` quantified over every `runtimeOk` configuration
  cannot follow from that invariant: it does not bound prior custom calls.
  Supply the budget at a successful C_CALL from `Fits` and represented counts.
- `BarrierGrowthFull` cannot preserve G1 quietness on a full table: overflow
  requests a minor GC. Standing decision: discharge via G2, retain its premise.
- C4 hand-proof expansion triggered the abstraction gate. Preserve the draft;
  the approved discovery round 2 waits until F1 is closed.
- Named-value WIP's former ASCII-only node predicate was stronger than
  `GoodF1`, whose primitive accepts arbitrary bytes. The byte/string and
  strcmp source bridges are now generalized; an ASCII guard on `GoodF1`
  remains a rejected route.
- `CustomMemCall` returning `Ready k` alone does not establish exact counter
  increment. A named counter-transition post is needed for n-to-n+1 accounting.

- `formatInteger` currently accepts `d/i/u/x/X/o`, flags, width and precision
  (`OCaml/Bytecode/Data.lean`), despite older F1 prose saying `%d`. A `%d`-only
  native summary can help whileMin but cannot discharge the general
  `F1CcallOpen.format_int_c_call2` field. Preserve that boundary explicitly.

- `F1Heap.NamedRoom` currently uses `maxNamed = 16` and `maxNameLen = 64`,
  but the claimed BcSem guards are absent from `primF1Impl` and `GoodF1`.
  Do not infer those bounds for every F1 call. Generalize the reserve using
  proved bounds, or surface a real domain decision before adding restrictions.

- 2026-10-27: a nursery-only `caml_format_int` return theorem cannot close
  the current general `GoodF1` field. `formatInteger` accepts widths such
  as `%2048d`; its result can exceed 256 payload words while remaining
  within `g1Budget.heapWords`. `Instr.minorAlloc` constrains opcode
  allocations, not this primitive result. The vendored `runtime/alloc.c`
  sends such strings through `caml_alloc_shr` and `caml_check_urgent_gc`.
  Preserve the current domain and prove the large-result path; do not
  silently infer a small-string bound from `Fits`. The fixed major-free-list
  pin in `F1Pins` must also be revisited for that path. This is source-level
  scope analysis, not a kernel-checked reachable-state counterexample.

- 2026-10-27: replacing the formatter's `hap1`/`hap2` stack bounds with
  only `ArgsOut` scalar ownership bounds leaves argument loads unreduced
  across stack writes; `svf_intQ_cases` then reaches the default heartbeat
  limit. Expose `ArgsOut.frames` (derived from `ArgsOut.out`) to `svf_mem`
  before symbolic execution, rather than expanding the resulting load terms.
  The interval consequence requires `0 < len`: an empty argument window
  inside a write frame satisfies `ArgsOut.out` vacuously.

- 2026-10-21: removing the ASCII conjunct only from `NamedNode` could not
  close the named-table bridge: `NamedTable.NodeAt.name` independently used
  `CString`, whose shared `Vsa.MemRepr.CStr.cons` required bytes below 128.
  The one-byte key `[0x80]` exposes that contract obstruction by inspection.
  The byte C-string/strcmp source interface has now been generalized and
  the library battery regenerated. Do not insert an ASCII guard into `GoodF1`
  or a premise excluding successful calls. The original inspection was not
  a kernel-checked counterexample.

- 2026-10-21: `StackGeometry.named` only separates named footprints from
  the VM stack. It does not justify the `.field` case of `LogWindows`:
  `StackGeometry.named_domain_alias` (`OCaml/Vm/Sim/NamedGeometryObstruction.lean`)
  is kernel checked and constructs that geometry with a placed named node
  at `Caml_state->extern_sp`, proving an eight-byte store there overlaps
  the named footprint. This refutes the geometry-only frame route, not
  reachability of the alias. Extend the physical separation/ownership
  invariant and its producers; do not hide the missing fact in `GoodF1`
  or a new premise excluding successful calls.

- 2026-10-21: the manager canceled overlapping build processes after earlier
  interrupted attempts. `scripts/lean-capped.sh` now owns the per-worktree
  `flock --close` serialization as well as the memory-cap policy. Retry
  through that wrapper; do not infer a proof failure from the cancellation.

- 2026-10-21 physical named geometry: allocator freshness cannot be framed
  by putting arbitrary named nodes into `f1Covered`. `NamedOwned H pl named`
  records actual `(node, requestedBytes) ∈ H`; `Gc.NamedOwned.fresh` derives
  fresh-record separation from that ownership. The current `LibHeapAt H`
  has no relation to `pl.nodes`/`world.named`, so it does not supply this
  ownership. This is an interface gap found by inspection, not a claim that
  a real malloc result aliases a live node.
- 2026-10-21 physical named geometry: actual node ownership alone does not
  discharge the custom-allocation part of `open_out_observed`. Its frame
  also requires `¬ state c x` for a named byte. `CustomMemCall.apart`'s
  `CallerApart.covered` excludes fixed extents, and `.records` excludes
  channels; `.free` excludes allocator metadata/free space, not all live
  blocks. A producer must establish that the custom table/state and named
  nodes have separate ownership. Do not add an unexplained successful-call
  premise or classify nodes as fixed extents to fill this gap. This is an
  inspection of the current contracts, not a checked execution obstruction.

- 2026-10-27: separating named nodes only from `f1Covered` and channel records
  omits the dynamically allocated remembered-set storage. Insertion writes
  that storage too. `namedBlocked` now includes its live `[base,end)` region
  when `base ≠ 0`; the startup, insertion and growth producers preserve it.
  This was an interface inspection, not a reachable alias counterexample.
- 2026-10-27: direct conversion between `(ch + chanOffBuff) + ioBufferSize`
  and `ch + 65608` hit the kernel recursion limit in the console named frame.
  Reassociate with `Nat.add_assoc` before converting the closed size. The
  focused `ConsoleCall` build passes without increasing recursion or heartbeat
  limits. This was a normalization failure, not a mathematical obstruction.
- 2026-10-27: the startup bucket proof cannot assume the checked log contains
  no stores to `named_value_table`: `decide +kernel` refuted that absence
  claim. Read the compact log's final byte view with `observedMem_bytes`;
  the stored values are zero. `WhileMin.namedBuckets` now checks that view.
- 2026-10-27 resolution of the selected-heap gap above: `LibHeapAt.named`
  carries a physical `NamedLedger` with `NamedOwned H`; footprint determinism
  matches it to the represented table. Channel-list entry likewise returns
  a ledger for the same `H` used by its allocation walk. Neither route
  infers ownership from arbitrary `HeapReady H`. Custom-state separation is
  explicit in the existing `CustomMemCall`/`CallerApart.named` contract;
  its concrete machine discharge remains open and is not inferred from `.free`.

- 2026-10-27: the captured major free block has only 126879 payload
  words (`Boot.WhileMinRuntimeReads.freeBlock`), below `g1Budget.heapWords`
  (262044). Thus a shrinking-singleton proof alone cannot cover every
  successful `formatInteger` result allowed by `Fits`; for example the
  width 1100000 is within the integer-format domain but exceeds that initial
  block. Reuse the existing `BestFitFallback.allocate_large` and
  `AllocLargeWrapper.allocate` where their premises hold, but retain heap
  expansion and the normal allocation wrapper's tracking obligations.
  The reviewed CustomCallPins also fixes stat_heap_wsz=0x1f000, and its
  PhysicalCustoms resource targets use the corresponding fixed denominator.
  A major-heap expansion changes that native read; the general formatting
  runtime must therefore generalize both the existing fixed free-list profile
  and this context/accounting specialization. Do not claim the fixed-ratio
  targets survive a changed heap size, or impose a new width guard on GoodF1.
  This is source-level scope analysis, not a checked reachable-state witness.

- 2026-10-27: a proposed unbounded named-key construction using repeated
  mutation of one byte buffer is outside the current F1 opcode domain:
  `SETBYTESCHAR` is F2 (`OCaml/Fragment.lean`). Do not use that construction
  as a GoodF1 counterexample. A bound from immutable key provenance still
  needs a proof; this observation does not supply the named reserve.

- 2026-10-27: the general `Skiplist.Ops` interface needs an ownership/room
  review before attempting its supplier. `live` quantifies over an arbitrary
  `HeapReady H` rather than a ledger carrying the actual cells, while
  `insert` has no explicit allocation-capacity premise. The first empty
  insertion milestone retains explicit capacity and selected ownership;
  it does not discharge this general interface. This is interface analysis,
  not a kernel-checked impossibility result.

- 2026-10-27: first empty skiplist insertion calls `caml_stat_alloc` at
  `0x8000bb2c`, certified by `jal_8002acbc_call_target`. Use the checked
  `stat_checked` interface at this splice. `stat_alloc_ready` is for the
  distinct `caml_stat_alloc_noexc` entry; it cannot be substituted directly.

- 2026-10-27: `LocalFrame.output` frames `vsaModel.out`, which is
  `Vsa.Machine.output = String.join sailOutput.toList`. Equality of that
  observation does not imply equality of raw output vectors. Compose the
  observable output frame, or prove a stronger shared execution property;
  do not extract a raw-vector frame from this weaker contract.
- 2026-10-27: do not assert a physical custom-count increment universally
  from the weak `CustomMemReturned` record. That record leaves the counter
  bytes in `state` unconstrained. Put the exact count in the actual named
  call-summary postcondition and carry its proof through channel callers;
  a separate implication from the old record does not supply that execution
  fact. The first custom-count WIP is preserved for this correction.

- 2026-10-27 counted-channel continuation: replacing the universal readiness
  field with `ChannelCountsAtCalls.atCall` derived from every ordinary
  `CcallSetupPost` repeats the same invariant gap. `VmPayload`/`WorldRepr`
  omit refcounts and physical custom counters; reachability of the BcSem
  state alone does not constrain those bytes of an arbitrary represented
  machine configuration. The draft blanket supplier was removed. Use
  `CountedVmReprAt`/`CountedCcallSetupPost` with explicit physical evidence
  and migrate their actual producers. Counted caller summaries cannot be
  silently cast to the weaker, universally quantified `PrimReturnsAtR`.
  This is contract inspection, not a checked reachable counterexample.

- 2026-10-27 unary setup/suffix continuation: the generated suffix's exact
  memory equality preserves the callee's physical successor count, but
  cannot turn `CountedResult.physical` into `ChannelCustomsRepr`. It copies
  whatever refcount bytes the callee returned. `CcallReturn` existentially
  selects a channel placement without retaining counted observations;
  `OutListReturned` permits refcount writes and exports a physical batch
  charge, without their natural readbacks. The opening's existing native
  `open_out_counts` must be retained at that same selected placement; the
  out-list needs increment/no-wrap observations as well. The earlier
  `counted_c_call1_arm` concluded only physical accounting. The complete
  return bundle now supplies those observations and retains complete
  `CountedRunning` at the same placement. Ordinary loop preservation remains
  open; do not recreate the weaker physical-only return interface.

- 2026-10-27 counted return readbacks: elaborating a `change` over the whole
  `writeLog (enterLog ...)` inside the large `ListedStep` context exhausted
  the default normalization budget. Factor the single SW readback over an
  abstract memory (`enter_refword` using `word32_writeLog`), then instantiate
  it after the shared record frame. This was a proof-normalization failure,
  not a mathematical no-wrap obstruction; do not increase heartbeats.
  Re-expanding the full prologue log for a four-byte epilogue observation
  likewise hits the default recursion limit; reuse `ProKept.bytes` from
  `pro_keeps` for that frame instead of unfolding the memory again.
- 2026-10-27: the first skiplist insertion worker's generated
  `SkipFirstEval` build exhausted its 12 GB cgroup (unit
  `run-p997545-i461614792.scope`, 18:42:17 UTC), killing the worker.
  The source checkpoint is preserved. Split/check the evaluator certificates
  and bound concurrent heavy compilation; do not raise memory or proof budgets
  or rerun the identical broad evaluator proof unchanged.

- The first skiplist retry also reached 12 GB at 18:48:05 UTC after splitting
  into per-instruction certificates using broad `simp [stepGM, ...]`; the
  exact failing declaration/cause was not isolated at that checkpoint. Diagnose it with `lean -M 6000 -j 1 --profile`
  and narrow evaluator simplification. Use `scripts/lean-guarded.py` so a failed
  or memory-heavy build cannot leave descendants consuming the worker cap.

- 2026-10-27, first-insertion evaluator diagnosis: the first failing
  declaration is `SkipFirstEval.i8002ab00_store`, not the long PRNG block.
  A temporary prefix checked with `-M 6000 -j 1 --profile` reports kernel
  excessive memory on its broad `simp` proof. Keep the symbolic stack
  address's `toNat` opaque; prove the sign extension and constant offset sum
  separately. Per-instruction splitting alone does not fix this route.
  Direct expansion of a concrete `wlogM` step also remains expensive;
  `checkedLogStep`/`checkedLogStore` compose the scalar certificates with an
  abstract tail. Concrete memory facts should rewrite the certified decoded
  instruction before applying the scalar window lemmas.

- 2026-10-27, first-insertion allocation composition: do not apply
  `stat_alloc_ready` directly at `jal_8002acbc_call.target`. The generated
  target certificate pins `caml_stat_alloc` (`0x8000bb2c`), whereas that
  summary starts at `caml_stat_alloc_noexc`. Compose the landed checked
  wrapper `stat_checked` and its allocator/frame result at the actual target.

- 2026-10-27: the formatter's former `snpAbove = 256` made the parsed
  format at `sp + 240` owned by `snpS (sp + 48) (sp + 16) 128`.
  The native `symbolic_summary` bridge requires its read-only data bytes
  outside that owned set (`LocalSeparation.bytes`), so the real caller
  could not use that ownership window. The seven spill slots occupy
  `[sp + 184, sp + 240)` exactly; the template now uses `snpAbove = 192`,
  ending ownership at `sp + 240`. Do not restore the wider window for
  this caller. This is an interface/interval obstruction, not a claim
  that a reachable formatter execution overwrites its format.

- 2026-10-27 G2 next-size split: the first continuation worker hit the
  12 GB cgroup cap at 20:55:32 UTC (`run-p4087439-i464873190.scope`).
  Generated `BestFitSplit` had passed 609 build jobs, then the `BestFitNext`
  build died before emitting a diagnostic. The exact declaration is not
  yet isolated. Preserve the WIP and diagnose source prefixes with
  `lean-guarded.py`, `lean -M 6000 -j 1 --profile`; do not repeat the broad
  build unchanged or raise the limits.

- 2026-10-27 G2 next-size split diagnosis: the temporary source prefix
  `/tmp/a6-next2-prefix.lean`, checked through the guard with
  `lake env lean -M 6000 -j 1 --profile`, isolates `BestFitNext.split_writes`
  as the first kernel excessive-memory failure. Broad `simp` over the
  generated chunk logs expands symbolic address observations. `simp only`
  over the log/scalar certificates checks without that expansion.
  The subsequent monolithic `split_access` also exhausts kernel memory;
  merely narrowing its address simplifier still times out at the final
  stack store. Compose bounded access plans with `accessPlan_append` and
  the existing `Native.nextSplit_piece*_regs/loads` certificates. The
  repaired complete continuation checks at the same memory/proof limits;
  do not restore whole-prefix reduction or increase budgets.

- 2026-10-27 next-size route representation: `BfShape.SmallShape` only
  constrains list links, readable link windows and heap placement. Its
  definition contains no block-header observation, so it cannot supply
  selected-list size/header agreement for `SplitInput.larger/small`.
  The complete route uses the original representation component
  `BfShape.SmallHeaders`, then derives the selected header size by list
  membership (`RouteInput.size`). This is a contract inspection, not a
  kernel-checked reachable-state counterexample; do not replace it with
  an unexplained header fact about an intermediate split state.

- 2026-10-27 named reserve review: bounding distinct immutable name keys does
  not bound all skiplist allocation calls. `callback.c:212` updates an
  existing node through `caml_modify_generational_global_root`; in
  `globroots.c:135-162`, UNTRACKED-to-OLD/YOUNG inserts a cell, while a later
  UNTRACKED value removes it (`skiplist.c:185` frees the cell). Replacing one
  existing name can therefore revisit the allocation path without creating
  another name node. This is a source/contract inspection, not a checked
  reachable-state counterexample or an assertion that native memory grows
  without bound. Key provenance bounds node/key allocation; a complete
  registration reserve also needs actual root-cell removal/reuse accounting.
  The current `FreeRoomEnd` preserves the same capacity `k`; do not silently
  treat it as a charge-refund theorem.
  Follow-up contract inspection (2026-10-28): `vsaRoomB` in
  `VsaIris/Vsa/HeapRoom.lean` measures `2*k + extendSlack <= heapEnd - top`;
  free chunks in bins do not contribute to this capacity. `fOK_chg` in
  `FreeRunAll.lean` uses only returned `top <= top0`. An interior free
  can therefore preserve this top-based bound without producing extra
  credit. General reuse needs a bin-aware resource invariant or a proved
  allocation route consuming the freed chunk; do not strengthen the existing
  post to `k + charge` by arithmetic alone. These are inspected definitions,
  not a checked reachable-state counterexample. Allocator files are generated
  from `experiments/syi/allocator-template` by `retarget_allocator_specs.py`.

- 2026-10-27, reset/backtrace continuation: the ELF's
  `caml_init_backtrace` (`0x8000ef3c`) only loads `Caml_state`, adds the
  generated `backtrace_last_exn` offset and tail-jumps at `0x8000ef48`
  to `caml_register_global_root` (`0x8000c9e0`). That wrapper tail-jumps
  at `0x8000c9f0` to `caml_skiplist_insert` (`0x8002aafc`). Neither wrapper
  initializes domain fields or creates another native return frame. The
  last-exception value must come from the executed domain stores, including
  the store of tagged unit at `0x8002a9bc`, and survive GC/stack/atom startup.
  `GcLowKeep` cannot supply that domain-word frame: it requires an address
  below `heapStart`, whereas the key is inside the owned domain allocation.
  Carry the domain observation through the actual producers; do not infer
  its value from the backtrace wrapper or a captured final memory. These
  are ELF and contract observations, not a kernel impossibility theorem.

- 2026-10-27, reset/backtrace domain readback: expanding the final quiet
  message's concrete `writeLog` inside `init_gc_finish` reaches the default
  recursion limit when framing the last-exception word. A low-global frame
  also lacks the domain allocation's natural upper bound. Use the shared
  `GcQuiet.word` certificate over an abstract entry memory and the existing
  `wordAt`/`MemSame` composition, with the concrete domain-word geometry
  checked separately. Do not raise recursion or heartbeat budgets to unfold
  the accumulated startup state.

- 2026-10-28 integer-format input extraction: `dsimp only` over the whole
  unfolded `formatInteger` success hypothesis exceeds the simplifier's step
  budget, as does `simp_all` with that rendering hypothesis in scope. The
  width/precision result expression duplicates symbolic replication and
  rendering terms. Expose only the outer rejection conditional with `change`,
  then the selected conversion conditional; leave their rendering remainder
  opaque. `formatInteger_conditions` checks at the default budget without
  evaluating the output or narrowing GoodF1.

- 2026-10-28 native format caller register projection: the generated prologue
  gives both sp and a2 as `R 2 + 18446744073709551568#64`. Asking
  `holds_project`'s Boolean certificate to select either as `R 2 - 48#64`
  made `caller_pro_arguments` fail kernel checking at 4 GiB; complete attempts
  reached the 10 GiB guard. Select the exact generated values first, then
  rewrite the scalar address equality in the resulting `GHolds`. The repaired
  isolated prologue/projection checks under 4 GiB with unchanged heartbeat
  limits. This is a proof-construction failure, not a native counterexample.
  Keep the caller's entry data, execution and returned observation as named
  phases. A returned length equation also needs the derived source-byte
  equality before transport between original/copied byte views. An extending
  structure must not name its format-list parameter `fmt`: `MeasureInput.fmt`
  is an inherited register observation and shadows that parameter.
