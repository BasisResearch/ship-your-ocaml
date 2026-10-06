# Lane a1-arms

## Current (F1 round, 2026-10-05)

Done (landed 741ad7a): `ArmSim` is stated over `LoopAt L P s c`
(`OCaml/Refinement.lean`). `StepsN.tick_lt` (`OCaml/Run/Clock.lean`, from the
new kernel law `Run.iter_inv`) makes the dispatch clock a run invariant.

Done (bf8de18 + next): `Running.stack : StackPlaced P s c`, the
`StackGeometry` of a representation witness (`OCaml/Vm/Sim/Invariant.lean`).
The VM stack window `[high - Layout.stackBytes, high)` lies above `.bss`, in
RAM, apart from `Caml_state`, code, placed objects, channels and primitive
entries (`Layout.stackBytes`, `stackThresholdBytes`, `domainStateBytes` are
compiler-measured by `gen_layout.py`). Every existing arm bridge now proves
it for its result:
* the shared restore lemmas take the pre-state geometry;
* `ArmInput`, `CcallResult`, `CcallSetupPost`/`CcallnSetupPost`,
  `RaiseContext`, `RaiseReentryReady`, `ModifyReturn` and `CaughtLogReady`
  carry it;
* the transports are `StackGeometry.state`/`same`/`frame_log`/`heap_set`/`alloc`.

Allocating restores (GRAB, CLOSURE, CLOSUREREC, MAKEBLOCK) take named
`stackApart`, `arenaEnd` and `arena` premises: the nursery object and the
allocation log are apart from the window and inside the allocator arena.

Done: `Running.native : NativePlaced c` (`∃ D, Invocation D c ∧ NativeValid
D`; bprime's snapshot and validity in `Invocation.lean`). Every arm bridge
preserves it:
* every arm write stays below `heapEnd ≤ D.nativeSp` (`StackGeometry.arena`,
  `domainArena`, `heapArena`);
* `x2` is restored, by register frames (`immediatePreserved`,
  `consumePreserved`, `callSavedRegs` now include `x2`; post structures carry
  `nativeSp`);
* C_CALLN's `sp + 88` spill is outside `invocationRanges`
  (`CcallnWriteOk.native`);
* raise/longjmp paths carry `NativeHeld` while `x2` is elsewhere.

Unconditional F1 table rows (`OpArm P (LoopAt L P) op`), derived through
`decode_fetch` (opcode and operand fetches from `decodeAt`) and the adapters
`opArm_of_next0/1/2` (`DecodeFetch.lean`):
* generated: ACC0–7, PUSH, PUSHACC0–7, ENVACC1–4, GETFIELD0–3, PUSHENVACC1–4,
  OFFSETCLOSUREM3/0/3, PUSHOFFSETCLOSUREM3/0/3;
* hand: CHECK_SIGNALS, POPTRAP, RESTART, PUSHTRAP, PUSH_RETADDR, APPLY1–3,
  OFFSETCLOSURE n, PUSHOFFSETCLOSURE n (`SignalRows`, `ControlRows`);
* hand: ACC n, PUSHACC n, POP n, ASSIGN n, ENVACC n, GETGLOBAL n,
  PUSHGETGLOBAL n, (PUSH)GETGLOBALFIELD n m, APPLY n, APPTERM n s,
  APPTERM1–3, RETURN n (`OperandTableRows`; RETURN takes `ExtraBounded P`).

Done: `Running.stack` carries `ArmGeometry` (`OCaml/Vm/Sim/ArmGeometry.lean`):
the `StackGeometry` plus a6-gc's `NurseryGeometry` of the same witness.
* Non-allocating arms frame the nursery through `YoungOutside log c`: the log
  misses `young_limit`/`young_ptr`. Every write certificate carries it,
  derived once from its window (`of_free`, `of_stack`, `of_windows` for VM
  windows).
* Allocating restores (GRAB, CLOSURE, CLOSUREREC, MAKEBLOCK) take one named
  `NurseryReserve c log a size count`. That is the allocation summary's
  young_ptr effect. `ArmGeometry.alloc_log` derives the old
  `placement`/`domainApart` premises from it and the nursery geometry.
* `ArmSim.entry` takes `ArmGeometry` at the cut. For whileMin it is the
  stack geometry with `Gc.whileMin_nurseryGeometry`.

* hand: RAISE, RERAISE, RAISE_NOTRACE, caught path (`RaiseRows`). Every
  quiet-raise premise comes from the loop head: `RuntimeFrame.barrier`/
  `backtrace` (a6-gc's pins), `NativeValid.rootSaved` (bprime) and
  `ExtraBounded.trapSaved` (a2-sem). An uncaught raise steps to the callback
  boundary at `pc = code.size`, which `GoodF1` makes unreachable
  (`uncaught_unreachable`): the rows take `GoodF1`, not a per-program premise.
* hand: C_CALL1–5 (`CcallRows`, generic `ccall_row_of`). `CcallReady` comes
  from the loop head: the generated `lookup` is word-aligned by construction,
  and the slots come from `StackGeometry.primsRam`. Named obligations remain:
  `CcallReturns` (a1-prims' callee summaries), `CcallEffects` (raise, exit
  and callback results) and `CcallArity` (per program).
  `CcallEffects` is retired: F1 primitives never raise or call back
  (`primF1Impl_ne_raise`/`_ne_callback`, `PrimOutcome.lean`), and only
  `caml_sys_exit` (one argument) exits. So C_CALL2–5 need nothing and
  C_CALL1 takes `CcallExit` (bprime's exit path).

* hand: GETFIELD n, PUSHENVACC n (`FieldOperandRows`), SETGLOBAL, SETFIELD n
  and SETFIELD0–3 (`BarrierRows`). caml_modify's summary is the GC lane's
  per-site obligation (`GlobalBarrier`, `FieldBarrier`, `FieldBarrierK`).
* bprime's generated `F1Table.lean` collects every row. Rerun
  `scripts/gen_f1_table.py` whenever a row changes.

Done: the G1 nursery room is in the loop invariant. `Layout.budget` is new.
`Running.stack`'s witness is `OCaml.LoopGeometry` (`ArmGeometry` plus
`G1Room L.budget s c`). Its transports have the same names
(`OCaml/Vm/Sim/LoopGeometry.lean`). Allocation consumes the room exactly
(`alloc_log`, count = size); no budget-fit premise is needed.

Primitive adapters for a1-prims (`CcallWriting.lean`):
* `ccall_writing_summary` (exact write log);
* `ccall_framed_summary` (`FramedCall`: footprint frame plus
  saved registers, the footprint below the native sp; console output).

Done: the allocation rows. MAKEBLOCK1–3, MAKEBLOCK n, GRAB (both paths),
CLOSURE and CLOSUREREC are proved (`MakeblockRows`, `MakeblockNRows`,
`GrabAllocRows`, `ClosureAllocRows`, `ClosurerecAllocRows`).
* The fresh location is re-placed at the reserved block (`Place.put`,
  `VmReprAt.put`): every represented pointer is live, hence present.
* `ReservedBlock`/`AllocLogOk.of_block`/`of_prefixed` derive every
  allocation log's certificates and `NurseryReserve` once.
* `FreshLogOk.of_windows` (`FreshLog.lean`) covers logs whose stores lie in
  the free nursery, the VM stack allocation or the young-pointer word.
  CLOSUREREC's pointer pushes overwrite consumed captures, so its log
  interleaves block and stack stores. `NurseryReserve.of_prefixed` is the
  reservation summary behind a prefix.
* `ClosurerecPlan` names a CLOSUREREC's loop-head premises. `.writes`,
  `.reserve`, `.arena` and `.machine` give every input of
  `closurerec_step_arm`.
* The runtime obligation is `AllocFrame L`. Its field `allocW` allows stores
  into the VM stack allocation as well as the free nursery. F1:
  `f1_allocFrame`, from a6-gc's `f1_allocFrame_core'`. `AllocFrame.alloc` is
  the nursery-only form, and `AllocFrame.prefixed` composes with a VM-stack
  prefix (CLOSURE's and CLOSUREREC's pushed accumulator).
* `opArm_of_next` is the adapter for any operand list (CLOSUREREC).
* No per-program premises: each allocation row reads its minor-heap size
  bound off the decoded instruction (`InF1.minor`, under `GoodF1`) through
  `opArm_of_next2_f1`/`opArm_of_decoded` and `GoodF1.inF1_at`. Major-heap
  allocations are outside F1 (`Fragment.majorAllocLedger`).

whileMin's `scratch` premise is gone: a2-sem's `Muldi3Any`/`udivdi3_spec_any`
specs write the scratch registers before reading them. No GPR-presence round
is needed.

STOP/uncaught-raise returns export the HTIF payload-counter frame
(`InterpRuntimeReturnPost.htif`, `UncaughtChecked.htif`) for bprime's exit.
`LoopRegisters.htifIdle` lands after a1-prims' `EffectPost.htifIdle`.

Done: `LoopRegisters.saved`: `s10`/`s11` (x26/x27, `unpinnedSaved`) hold
values at every loop head; C paths spill them (caml_sys_exit's and the console
primitives' prologues). `CcallSetupPost.calleeSaved` gives all of `s0`–`s11`
at the callee entry (`vmSaved`: VM sp, accu, next-code pointer).
* The other callee-saved registers are pinned already. They hold the VM
  registers, the loop constants and the native `sp`; `s7` is dispatch's
  next-code pointer (`DispatchPost.nextCode`).
* Arms that don't write `s10` keep it through `loopPreserved`.
* MAKEBLOCK, CLOSURE and CLOSUREREC pin it (`saved_of_pin`, through
  `loopRegisters_of`).
* Entry gets it from `InterpCaller.gprs` (`GprPresent.saved`). The raise path
  carries it in `RaiseContext.saved`, and longjmp's restored registers give
  `ReentryControl.s10`.
* All-31 GPR presence would need a1-prims' `EffectPost` to carry presence of
  the written temporaries (~85 files). a6-gc states malloc's need as one named
  premise of caml_modify's realloc branch.

Done: channel records at full extent (`chanOffBuff + ioBufferSize`) in
`StackGeometry` (channels, heapChannels, domainChannels, channelArena, and the
new channelCode/channelAtoms/channelPrims/channelsApart) and in
`WindowSeparated.channels`. `PayloadOutside`/`PayloadCoreOutside.channels`
use it too, plus `openHead` (the open-channel list head).
`channel_copied_full` narrows to the buffer with `ChanAt.bufferLe`.
`transport_ids` (Stack/Nursery/Arm/LoopGeometry) needs only the same channel
ids, so channel primitives can change record contents. `frame_log`/`alloc_log`
take the certificate's `channels`/`openHead`, which give a6-gc's
`channelsListed` its list head and record links (`links_of_channels`);
`frame_vm` derives both from its VM windows (`VmWindow.channel`/`openHead`).

Done: `LoopRegisters.gp` (x3 = newlib's `gpV`). Every arm frames it,
entry takes it from `InterpCaller.gp`, and the raise paths carry it
(`RaiseContext.gp`, `ReentryControl.gpEq`, `CaughtLogReady.gp`).
`CcallSetupPost.libraryReady (setup) (gprs)` gives `LibraryReady` at a C_CALL
entry. GPR presence is still an argument; next is the sweep making it a loop
field (C_CALL returns rebuild it from a1-prims' `GprsKept`, arms via
`GprsKept.of_segment`).

Row premises for generic `L`:
* `MemoryStable L.runtimeOk` and `RuntimeFrame L high dom`; both discharged
  for a6-gc's pinned `Gc.f1Layout` (`f1_memoryStable`, `f1_runtimeFrame`,
  `F1Frame.lean`);
* `StackCapacity B` (budget + 2·Stack_threshold ≤ Stack_size);
* BcSem reachability invariants from a2-sem: `ExtraBounded` (RETURN, GRAB)
  and trap ≤ stack length (PUSHTRAP).

Certificates are proved once and reused:
* `StackLogOk.of_window`: any word log in the stack allocation;
* `VmLogOk.of_windows`: logs that also write VM-owned Caml_state fields;
* `ApplyWriteOk`, `TailcallWriteOk`, `ApptermWriteOk`, `RetaddrWriteOk`,
  `PushtrapWriteOk`, `TrapWriteOk`, `RestartInput`, `AssignWriteOk`,
  `PushWriteOk` `.of_geometry`.

`StackGeometry` places the stack, the Caml_state record, code, atoms and
objects pairwise apart. bprime's entry supplies it at the cut.

Open, next:
* Writes outside the VM stack (SETFIELD n, SETGLOBAL, trap and C_CALL
  setup Caml_state stores) need runtime framing beyond `RuntimeFrame`'s
  stack windows. Decide the contract with a6-gc (runtimeOk's footprint is
  the Caml_state record plus allocator metadata).
* `raiseBuf` (the Invocation field for `caml_raise`'s external path):
  deferred, off whileMin's path.

## Shared heap-field update facts

`live_field_edit` proves that writing an already-live value introduces no new
reachable objects. `heap_set_size` and `heap_field_edit` factor unchanged
footprint sizes and heap separation from concrete object readbacks.
`block_field_written` proves the exact one-word update, retaining the header
and other fields. `field_log_outside` derives neighbour separation from the
represented heap; `heap_field_written` combines those observations with the
shared heap-graph law and existing object-copy combinators. These facts cover
integer OFFSETREF updates and later pointer-field writes.

Capped/default-limit builds pass: heap graph 0.8s, concrete field store 0.9s.
All new headlines are audited. PUSH_RETADDR landed as `4296303`, full gate
passing. Coverage remains 107 conditional opcode bridges. Next: frame the
non-heap payload around OFFSETREF, then compose its generated body and
corrected operand-width arithmetic.

## Represented PUSH_RETADDR arm

`retaddr_stored` proves the three write-log readbacks; `retaddr_payload`
uses the shared finite stack prefix and root transport. `retaddr_restore`
restores image, primitive bindings, runtime, loop registers and represented
data. `push_retaddr_arm` and `push_retaddr_step_arm` connect that restoration
to the generated eleven-instruction body and the real semantic transition.
Return-target, stack-space/separation and runtime-window premises remain
explicit; saved extra arguments are tagged correctly for every Nat value.

`stack_decrement`, `image_entry_code` and `word_after_writeLog_at` factor the
repeated address, code-frame and readback adaptations. Fixed C_CALL setup
generation and C_CALLN now reuse them. Capped/default-limit builds pass:
return-frame restoration 0.9s, full arm 1.2s. New headlines are audited.
Machine bodies/stack-prefix facts landed as `ff3c5f6`, full gate passing.
There are **107 conditional represented opcode bridges**. Next: heap update
and root framing for OFFSETREF, then the remaining control/allocation arms.

## OFFSETREF and PUSH_RETADDR machine bodies

`tr_offsetref` proves the eight-step read/modify/write body with exact opaque
load equations and one store. `tr_push_retaddr` proves the eleven-step return
frame push, with all three stores in the generated memory log. Both include
full-image code projections and generated code-store frame proofs. Separate
capped/default-limit builds pass: OFFSETREF 1.5s, PUSH_RETADDR 2.6s.

`stack_prepend` and `payload_stack_prepend` factor finite return/application
frame indexing and root transport through the existing stack-payload rule;
the capped build passes in 0.8s. All new headlines are audited. The block
SWITCH bridge landed as `14842e3`, full gate passing. Coverage remains 106
conditional represented opcode bridges. Next: instantiate the shared stack
prefix with PUSH_RETADDR readbacks, then restore its represented state; heap
update/root framing for OFFSETREF follows.

## Represented block SWITCH path

`SwitchTag.of_object` derives the semantic tag and native header byte from
an ordinary represented object; `SwitchTag.read` frames it through dispatch.
`switch_count_read` derives the unsigned halfword from the represented packed
size operand. `switch_block_arm` consumes these observations and the generated
12-step body; `switch_block_step_arm` extracts bounds and target success from
the real bytecode rule. Native and semantic packed-size naturals are equated
only after proving nonnegativity from successful selection.

Capped/default-limit builds pass: read/semantic facts about 0.8s each, full
block bridge 1.1s. All new headlines are audited. Integer SWITCH landed as
`84fc3fe`, full gate passing. Both SWITCH cases now have conditional represented
bridges, bringing coverage to **106 opcodes**. Atom/infix tag headers, read
geometry and full invariant adapters remain explicit obligations. Next:
OFFSETREF and PUSH_RETADDR machine families, then their shared write effects.

## Represented integer SWITCH path

`switch_int_arm` reads the selected represented table word and follows its
signed displacement relative to the table start. `switch_int_step_arm`
extracts nonnegativity, bounds and target success from the actual semantic
step; decoded table/represented operand agreement remains explicit.
`switch_int_scale` reuses `longVal_native`, and `switch_table_word` factors
the table addressing algebra. The capped/default-limit bridge build passes
in 1.0s, with arithmetic 0.8s; all new headlines are audited. Machine paths
landed as `9132dc1`, full gate passing. The block-tag path is next. Coverage
is 105 conditional opcode bridges plus the integer SWITCH case; the full
SWITCH bridge and lane exit remain open.

## SWITCH machine paths and total LHU

`tr_switch_int` and `tr_switch_block` prove the census-derived 10- and
12-instruction native paths, retaining guards, read geometry and complete
frames. The shared unsigned-load emitter now supports LHU through the landed
`exec_lhu_ramv`; the classifier and segment def/use logic retain its 16-bit
zero extension. A regression test covers width, repeated source/destination
and rejected x0 operands. All seven generator tests pass.

Separate capped/default-limit builds pass: integer body 1.8s, block body 2.0s.
The block path uses the existing exact opaque-load equations; expanding its
nested loads was stopped after about a minute at 14 GiB and replaced by this
existing abstraction, with no budget increase. Represented SWITCH selection
and target adapters remain next. CHECK_SIGNALS landed as `45d4a42`, full gate
passing. Coverage remains 105 conditional represented opcode bridges.

## Represented CHECK_SIGNALS arm

`check_signals_arm` and `check_signals_step_arm` cover the no-pending path
through its shared native block. The generator follows an internal direct
jump to an explicit census-derived exit, retaining the branch guard in the
segment contract. `signalCheckReady_of_runtime` derives the zero flag from
the concrete runtime invariant. The fixed pending-flag address and its
proved read geometry use Layout; no new data-address literal or read-window
premise is introduced. Capped/default-limit builds pass: body 1.0s,
represented bridge 0.9s. All headlines are audited. MULINT landed as
`b113daf`, full gate passing. Coverage is **105 conditional represented
opcode bridges**; remaining arithmetic, heap and control families are open.

## Represented MULINT arm

`mulint_setup` establishes the libgcc operands, link register, popped stack
and caller frame from the generated prefix. `mulint_callee` consumes the
proved library summary; `mulint_return` retags the product through the
generated suffix. `mulint_arm` and `mulint_step_arm` compose these using
`callSeg` and the shared consuming-arm restoration. No multiplication callee
premise remains. `MulintScratch` explicitly names the two defined scratch
registers required by the copied specification; the full invariant still
needs to supply it, read geometry and runtime framing.

Capped/default-limit builds pass: call/return 0.9s, setup 1.0s, full arm 0.8s.
All new headlines are audited. Library/arithmetic landed as `f203e10`, full
gate passing. There are now **104 conditional represented opcode bridges**.
Next: CHECK_SIGNALS and remaining arithmetic, mutation/allocation/control
families; unconditional ArmSim, entry/halt and machine whileMin remain open.

## MULINT library adapter and arithmetic

`muldi3_summary` exposes the landed total libgcc proof as a `FnSummary`
with named input/result fields, exact memory/output preservation and the
complete register frame. `muldi3_post_named` destructures the copied result
once. Its code pins come from the executable image through the same
generator projection used by arm bodies. `tag_truncate` and `tag_mul_native`
prove the native signed operands/product retag to the modular 63-bit product.
Capped/default-limit builds pass: library adapter 0.8s, arithmetic 0.8s.
Machine boundaries landed as `752449d`, full gate passing. The represented
prefix/callee/suffix composition is next; coverage remains 103 bridges.

## MULINT machine call boundaries

`tr_mulint_prefix` runs the five instructions through the direct JAL to
`__muldi3`; `tr_mulint_suffix` runs the four return instructions back to the
loop head. Both retain exact register/memory/output frames and project code
pins from the pinned image. The generator now ends direct-call prefixes at
callee entry, leaving callee execution to the shared call composition.
Separate capped builds pass at default limits: prefix 1.3s, suffix 1.0s.
The new headlines are audited. OFFSETINT landed as `4cd5b6a` with the full
gate passing. Coverage remains 103 conditional represented opcode bridges;
MULINT still needs the represented adapter to the landed libgcc summary.

## OFFSETINT with corrected operand width

`offsetintOperand_eq` proves the generated LW/SLLIW operand contribution is
exactly the sign-extended 32-bit shifted word. `tag_offsetint` reuses
`tag_untag_odd` and the operand's low bit to recover the exact native tagged
result. `offsetint_arm` and `offsetint_step_arm` now simulate the corrected
semantics through the generated body and shared immediate restoration;
no narrow-operand restriction is needed. `offsetint_width_obstruction`
remains as a regression witness against the previous 64-bit-shift model.

The targeted capped/default-limit build passes (about 1 second for the arm),
and all new headlines are audited. C_CALLN setup/composition landed as
`bad2825`, full gate passing after rebases onto shared GC comparison facts,
argv caller effects and mopup queue work. There are now **103 conditional
represented opcode bridges**; entry/halt and full invariant adapters remain
open. Next: remaining arithmetic and memory-update families, starting with
MULINT's generated call boundaries and the landed libgcc summary.

## Returning C_CALLN arm

`c_calln_setup` establishes the stack-array ABI from the generated 21-step
prefix: two operand reads, five exact stores, preserved represented payload,
argument array, saved native/VM frame and ELF-bound target. `CcallnWriteOk.stored`
and `ccalln_array` derive the stored words and argument representation through
shared write-log and stack predicates. `writeWindow_nat` now factors native
store geometry in both fixed-arity and N setup adapters.

`c_calln_arm` and `c_calln_step_arm` compose dispatch/setup, the named
`CcallnCallee` primitive summary and the represented return through callSeg.
`c_calln_callee_of_readOnly` adapts a represented stack-array ABI summary;
it does not assert that fixed-arity primitive summaries implement that ABI.
The actual callee summary remains a1-prims' named obligation. Setup geometry,
runtime frame laws and positive/count bounds remain explicit.

Capped/default-limit builds pass: store/array facts about 1.0s, input about
0.8s, setup 2.7s, full arm about 1.0s. All new headlines are audited; generator
and discipline checks pass. The represented N return landed as `8f2bdb8`,
full gate passing. There are **102 conditional represented opcode bridges**.
Entry/halt, exception/exit continuations, invariant adapters and the lane
exit are still open.

Next: OFFSETINT against the landed corrected 32-bit operand shift, then
remaining arithmetic, heap mutation/allocation and control families. The
old `OffsetWidth` obstruction remains a checked regression witness against
the previous operand interpretation; it no longer describes the current
OFFSETINT/OFFSETREF semantics.

## C_CALLN represented return

`CcallResult` now holds the represented primitive result separately from
caller-owned frames. `ccall_primitive_result` consumes a1-prims' postcondition;
`ccall_result_restore` performs the shared payload/root/platform restoration.
The fixed-arity contracts and theorem interfaces are retained.

`CcallnSaved` names the native saved-PC slot, ABI-preserved argument count,
native stack pointer, VM saved environment/extern_sp and read geometry.
`CcallnSaved.frame` preserves these across read-only callees;
`c_calln_primitive_return` and `c_calln_readOnly_summary` adapt represented
primitive summaries. `c_calln_return` runs the generated eight-instruction
suffix and restores Running with count-minus-one stack values dropped,
under positive-count and stack-length bounds. Its Triple adapter supports
the forthcoming callSeg composition. The capped/default-limit targeted
build passes in 1.1 seconds, and all new headlines are audited.

The C_CALLN machine boundary landed as `0eb285d`, full gate passing after
adopting callback semantics and primitive allocation work. Coverage remains
101 conditional complete opcode bridges. Next: the five-store represented
setup and stack-array ABI input, then named callee composition.

## C_CALLN machine boundary

`tr_c_calln_prefix` runs the 21-instruction stack-array setup through JALR;
`tr_c_calln_suffix` runs the eight-instruction return. Both come from the
existing arm generator, with exact memory effects, compact prefix register
frames, full-image pins and Layout checks. Address-construction discovery
now follows instruction shape, supporting both fixed-arity and N calls.
The prefix's capped/default-limit build passes in 8.0 seconds; the suffix
also passes separately. These add no represented opcode bridge yet.

Fixed-arity arm composition landed as `5e05c63`, with the full gate passing.
Coverage remains 101 conditional represented bridges. Next: describe the
C_CALLN stack-array input and saved native-PC/count frame, prove represented
return/setup, then consume its named primitive summary premise.

## C_CALL2–C_CALL5 represented arm composition

`c_call2_arm` through `c_call5_arm` and their `step_arm` adapters compose
dispatch, the generated represented setup, `CcallCallee.summary`, and the
generated return bridge through callSeg. The bytecode adapters use the
explicit stack-length bound to match the model's consumed argument count.
The shared `CcallReady` and `CcallCallee` contracts retain the unary API;
`ccall_callee_of_readOnly` adapts a1-prims' represented read-only summaries
for every fixed arity. `c_call2_int_compare_callee` supplies a concrete
binary instance using the landed integer-comparison summary.

Separate capped/default-limit builds pass (1–2 seconds per arm composition),
as do regeneration and discipline checks. The headline theorems and concrete
callee instance are audited. Represented setup landed as `fef53a2` with the
full gate, after preserving a1-prims' executable-name ledger update.

There are now **101 conditional represented opcode bridges**. Fixed-arity
C_CALL arms cover returning `.ok` primitives under named callee and call-site
premises. C_CALLN, primitive exception/exit continuations, remaining arm
families, invariant adapters, entry/halt and the lane exits remain open.
Next: generate C_CALLN's distinct stack-array ABI prefix and return boundary.

## Fixed-arity represented setup

`CcallSetupPost` names the represented primitive input, saved caller frame,
and bound target at any fixed-arity return PC. `CcallArguments` records the
finite stack-length/read-window obligation. `ccall_argument_load` frames
argument words through the exact saved-frame writes; `ccall_arguments_repr`
assembles accumulator plus stack-prefix arguments in consecutive ABI registers.

`scripts/gen_ccall_setups.py` now generates setup adapters for arities 1–5,
deriving load order and register positions from the machine segment JSON.
`c_call2_setup` through `c_call5_setup` establish the represented boundary
without assuming any primitive execution. Separate capped builds pass at
default limits (roughly 3–4 seconds per adapter), including the existing
unary arm after factoring. The generator has a gate drift check; shared
lemmas and each setup theorem are in the axiom audit.

The shared return family landed as `bef25f2`, full gate passing. Next:
compose C_CALL2–C_CALL5 setup, named returning primitive summaries and
restoration with callSeg; then handle C_CALLN. Coverage is still 97 conditional
complete opcode bridges until those compositions land.

## Fixed-arity represented returns

`CcallReturn` separates the common represented primitive postcondition from
its return PC. `ccall_primitive_return` and `ccall_readOnly_summary` consume
a1-prims contracts at any fixed-arity call boundary. `ccall_return_restore`
uses `payload_stack_drop` to retain the returned accumulator as a root while
removing consumed arguments. The saved-frame interface remains compatible
with the landed unary setup and primitive summaries.

`scripts/gen_ccall_returns.py` emits `c_call1_return` through
`c_call5_return` and their Triple interfaces from the generated suffix
specifications. These run the pinned six-instruction suffixes, restore
Running, and drop exactly arity-minus-one stack words under an explicit
length bound. The C_CALL1 theorem keeps its existing interface. Separate
capped builds pass at default limits (about one second per return adapter);
the complete C_CALL1 setup/callee composition also rebuilds successfully.
Generator drift, discipline and abstraction checks pass; headline audits
are included. Machine families landed as `155074a` with the full gate.

There remain 97 conditional represented opcode bridges: returns alone do
not discharge C_CALL2–C_CALL5. Next: generate their represented setup and
argument register bundles, then compose them with named callee contracts.

## C_CALL2–C_CALL5 machine families and GcSafe rebase

`gen_arm_pilot.py` now generates each fixed-arity call's prefix through JALR
and its six-instruction return suffix, including local/full-image pins, store
frames and Layout address checks. A single arity-driven shape covers 2–5;
opaque load observations and compact register frames reuse the C_CALL1 route.
Separate capped/default-limit builds pass: prefixes 4.3s, 4.5s, 4.7s and
5.9s; suffixes 1.3–1.4s. These are machine certificates, not additional
represented arm bridges.

The returning C_CALL1 arm landed as `8e2eb02`, full gate passing after
automatic rebases onto boot startup, primitive copy-string summaries, and
the approved GC contract (`025786c`). `ArmSim`, refinement and headline
statements now carry `GcSafe P`; Good and Fits are unchanged. No local
weakening of those statements was introduced.

There are still 97 conditional represented opcode bridges. Next: factor
the represented return contract/template across arities 1–5, including
bounded stack consumption, then generalize setup and named callee composition.
C_CALLN, primitive exceptions/exits, entry/halt and lane exits remain open.


## C_CALL1 arm composition

`c_call1_arm` and `c_call1_step_arm` compose dispatch, the proved generated
setup, `Ccall1Callee.summary`, and generated represented restoration via
`callSeg`. `Ccall1Callee` is a named returning-primitive obligation: an F1
semantic `.ok` result and a represented machine call summary retaining the
saved caller frame. It does not assume execution of the opcode arm.
`c_call1_callee_of_readOnly` consumes the existing a1-prims postcondition;
`c_call1_sys_argv_callee` cites the landed Sys.argv summary with an explicit
runtime/world argv-global binding. Primitive exceptions and exits remain open.

Default-limit/24 GiB build: 2.5s. Setup landed as `c65fa8c`, full gate passing
after rebasing a1-prims' nursery-layout and copy-string boundary landings.
There are now 97 conditional represented opcode bridges, counting C_CALL1
for successful returning primitives. Next: generalize the call family to
C_CALL2–C_CALL5 (same saved frame, additional arguments and stack consumption),
then C_CALLN. The approved GcSafe threading has since been adopted.


## C_CALL1 represented setup

`c_call1_setup` derives the represented `ImmediateInput`, saved caller frame
and ELF-bound primitive target from the generated prefix. `Ccall1WriteOk`
names the static three-store geometry/separation. The payload, image and
primitive bindings use existing write-log frames; saved words reuse
`read64_of_writeLog_at`. Domain and primitive-table addresses are checked
against Layout by generated equalities. All data addresses come from Layout.

The first adapter exposed the cost of repeated register-noise lists in long
segments. The generator can now compact exported frames using
`StepFrameOut.widenChecked`, a finite reflected inclusion certificate. An
initial propositional normalization timed out; the checked list inclusion
builds at default limits. The prefix is 9.8s and represented setup 13s,
under the 24 GiB cap. `LogRead` shares total-word observations with PUSH.

The return bridge landed as `8ab381c`, full gate passing. Next compose
dispatch/setup, a named represented callee obligation and generated return
with `callSeg`. The opcode count is still 96 pending that composition;
primitive exceptions/exits, the rest of F1 and all lane exits remain open.


## C_CALL1 represented return and primitive consumption

`c_call1_return` restores `Running` through the six-instruction generated
suffix from `Ccall1Return`. Its caller-owned `Ccall1Saved` frame is separate
from the primitive result payload/platform. `c_call1_primitive_return` consumes
a1-prims' `PrimitivePost`; the read-only adapter proves saved-word/register
preservation from the callee memory/frame contract. `c_call1_sys_argv` cites
the landed `caml_sys_argv_primitive` and composes it with return restoration
using the shared `c_call1_resume`. No primitive body is reproved.

`loopRegisters_frame` factors the fixed-register reconstruction out of the
existing accumulator, stack and new C-call restorations. Default-limit builds
pass (return and adapter: 1.2–1.4s). Machine boundaries landed as `38b639a`,
full gate passing. The represented opcode count remains 96: C_CALL1 still
needs its prefix-to-primitive payload/saved-frame adapter and full dispatch
composition. Read/write geometry and runtime frame assumptions remain explicit.


## Generated C_CALL1 machine boundaries

Rebased against main and regenerated the image, arm, ALU and dispatch artifacts;
the fixed `.embed` migration was already included and regeneration had no drift.
`GcSafe P` threading was adopted at `025786c` in the subsequent call-arm landing.

`tr_c_call1_prefix` proves the 17-instruction setup through the indirect call,
including the saved environment/PC and extern_sp stores. `tr_c_call1_suffix`
proves the six-instruction restoration after return. Both are generated from
the census with exact memory effects, output and register frames, and full-image
pin projections. JALR now flows through the classifier, site generator, segment
generator and `chain_frame_out`; `pins_jalr` reuses `pins_of_frame`. The prefix
uses opaque load words with exact equations and fetch pins spanning two chunks.

The generated prefix builds in 7.3s and suffix in 9.3s under default limits
and the 24 GiB cap. These are machine boundaries, not a represented C_CALL1
bridge: 96 conditional represented opcodes remain. Next connect the boundaries
through named a1-prims contracts, restoring the represented state after return.


## ASSIGN and shared stack-edit frames

`assign_arm` and `assign_step_arm` prove the in-place stack update and unit
result through the generated seven-instruction store body. `stack_assign`
checks the overwritten word and preserves every other slot; `assigned_root`
retains only already live values. `payload_frame_stack` reuses the existing
whole-payload frame on an empty-stack view and `object_copied` for the
original live heap, then installs the new stack. `StackEditOutside` names
the required non-stack and heap separation.

Before introducing a third register/dispatch reconstruction, the common
parts were factored as `StackPost.registers`, `loopRegisters`, and
`after_dispatch`. Existing consuming and PUSH bodies now use them.
`image_word_code` similarly shares the store-versus-fetch range argument.

Default-limit/24 GiB builds pass for the frame/restoration modules
(0.9–1.0s each) and represented ASSIGN bridge (1.1s). The preceding vector
length landing is `86dbfaf`, full gate passing after the memcpy rebase.
There are now 96 conditional represented opcode bridges. Next: primitive
call setup/restoration and remaining heap-write/allocation/control families.
Full `ArmSim`, entry/halt, semantic-domain corrections and lane exits remain open.

## Header size and VECTLENGTH

`vectlength_arm` and `vectlength_step_arm` reuse `header_words` from the
primitive lane and shared immediate restoration. `SizeSelection` records
the represented accumulator, semantic size and header word count.
`SizeSelection.of_object` derives it at an ordinary allocation base from
`ObjAt`; atoms/infix pointers still require their own header agreement.

The initial generated load/shift body expanded its total memory read and
reached about 14 GiB after a minute; that owned build was stopped. The
generator now supports opaque loaded-word parameters with exact equations
via its existing rewrite interface. VECTLENGTH uses one, and the unchanged
semantic body builds in 1.3s, with the represented bridge in 984ms, under
24 GiB/default limits. Other families retain their existing generated output.

The physical equality landing is `cd6591f`, full gate passing. There are
now 95 conditional represented opcode bridges. Next: remaining stack/heap
writes, allocation and primitive-call setup/restoration. Full `ArmSim`,
entry/halt, semantic-domain corrections and lane exits remain open.

## Physical equality arms

`eq_step_arm` and `neq_step_arm` consume successful physical-equality
`stepI` results and compose both generated native paths through shared stack
consumption. `WordEquality.reflects` is the named static condition equating
abstract physical equality with equality of represented words; it makes no
execution assumption. `WordEquality.ints` discharges it for all tagged
integers via `untag_tag`. General pointer/value injectivity remains an
invariant-adapter obligation and is not inferred from current placement alone.

Separate 24 GiB/default-limit builds pass: bodies 1.0–1.7s, path bridges
1.1–1.5s, compositions 1.0–1.1s. The preceding integer equality-branch
landing is `d090876`, full gate passing. There are now 94 conditional
represented opcode bridges. Next: header/length reads, then remaining stack
and heap stores, allocation and calls. Full `ArmSim`, entry/halt, semantic
domain corrections and lane exits remain open.

## Integer equality branches and pointer guard gap

`beq_step_arm` and `bneq_step_arm` consume successful `stepI` results
with an explicit integer-accumulator premise. Both paths use the existing
comparison-branch generator, `longVal_native`, control restoration and
relative-code arithmetic. BEQ takes the native equality branch on a semantic
jump; BNEQ takes it on semantic fallthrough. No new guard assumption is used.

`BranchCompare.beq_pointer_guard_obstruction` (in namespace `OCaml.Vm.Sim`)
checks that shifting pointer word `0x80000000` produces immediate
`0x40000000`, making the native equality guard true. Abstract physical
equality is false, and `beq_pointer_falls_through` checks the actual pointer
BEQ rule. This is a word/semantic-rule discrepancy, not a full Loaded/run
counterexample. The arbitrary pointer word is not a fixed ELF data address.
A2-sem needs to resolve this non-integer domain alongside the OFFSETINT/REF
width and negative-index gaps; those gaps were not hidden by changing the statement.

Separate 24 GiB/default-limit builds pass: BEQ bodies 1.9s/2.8s, path
bridges 1.5s; BNEQ path bridges 1.2s/1.6s and composition 1.2s. The
preceding nested-field landing is `f7d5deb`, full gate passing. There are
now 92 conditional represented opcode bridges. Next: EQ/NEQ with named
word-equality reflection, then remaining stores, allocation and calls.
Full `ArmSim`, entry/halt and lane exits remain open.

## Composed global-field loads

`getglobalfield_arm` and `pushgetglobalfield_arm` compose two represented
field selections with `FieldSelection.read_reachable`. The old direct-root
read API remains a specialization. `word_frame_reachable` and `load_frame`
preserve reachable field observations through a separated write log, so the
PUSH variant derives the intermediate pointer before applying its generated
body. One new generator emits both variants and is checked by check_all.

Separate 24 GiB/default-limit builds pass: bodies 5.6s/7.7s (12/14
instructions), bridges 1.7s/1.6s. The preceding global-read landing is
`8cd1244`, full gate passing. There are now 90 conditional represented opcode
bridges. Next: remaining comparisons, stack/heap writes, allocation and calls.
Full `ArmSim`, entry/halt, semantic-domain corrections and lane exits remain open.

## Global-root indexed loads

`getglobal_arm` and `pushgetglobal_arm` reuse the indexed-read and push
generators. The source pointer is derived from `VmReprAt.globals` and the
selected root placement, with the global address checked against Layout.
The PUSH variant frames that binding and selected field through the stack
store using the existing payload separation. Existing generated families
are unchanged by these extensions.

Separate 24 GiB/default-limit builds pass: bodies 2.1s/3.1s, represented
bridges 1.2s/1.3s. The preceding PUSH landing is `62bbdfd`, full gate passing.
There are now 88 conditional represented opcode bridges. Next: the nested
GETGLOBALFIELD/PUSHGETGLOBALFIELD selections. Full `ArmSim`, entry/halt,
semantic-domain corrections and lane exits remain open.

## Indexed and atom PUSH families

`pushacc_arm`, `pushenvacc_arm`, `pushatom0_arm` and `pushatom_arm`
reuse the common push generator. `pushedWord`, `pushed_value`, `pushed_root`
and `PushWriteOk.pushed_read` cover selection from the pushed stack, including
index zero (the saved accumulator). Environment selection reuses the field
frame; atom loads use `PushWriteOk.word_read` with the payload atom-global
separation and the runtime table binding. All data addresses come from Layout.
Nonnegative operand and RAM-window premises remain explicit for indexed arms.

Separate 24 GiB/default-limit builds pass: bodies 1.6–2.7s, bridges 1.1–1.2s.
The prior operand-prefix landing is `77f9d50`, full gate passing. There are
now 86 conditional represented opcode bridges. Next: global-read families
and their PUSH variants, then the remaining write/allocation/call families.
Full `ArmSim`, entry/halt, semantic-domain corrections and lane exits remain open.

## Operand-driven PUSH prefixes

`pushconstint_arm` and `pushoffsetclosure_arm` save the accumulator, read
the preserved operand, and restore the complete represented result.
`PushWriteOk.operand_read32` derives that read from the existing payload
write separation and `OperandAt`; the generated body instantiates its opaque
post-store memory before using the read. Signed closure offsets reuse
`ClosureOffset`, including negative operands with nonnegative destinations.

Separate 24 GiB/default-limit builds pass: bodies 1.5–1.7s, bridges 1.1s.
The fixed PUSH closure-offset landing is `043c033`, full gate passing.
There are now 82 conditional represented opcode bridges. Next: variable
PUSHENVACC/PUSHACC, using the same operand-preservation and payload frames.
Full `ArmSim`, entry/halt, semantic-domain corrections and lane exits remain open.

## Fixed PUSH closure offsets

`pushoffsetclosurem3_arm`, `pushoffsetclosure0_arm` and
`pushoffsetclosure3_arm` reuse `ClosureOffset` and `push_value_arm` in the
shared push generator. The machine generator follows the census entry through
fallthrough prefixes to the actual terminal jump, so the two-instruction
PUSH prefix and its common suffix form one checked five-instruction body.
The old accumulator is saved before the adjusted environment pointer becomes
the result; its allocation identity remains live.

All three families pass separately under 24 GiB/default limits: bodies
1.5–3.3s, bridges 1.2–1.6s on the shared host. Existing artifacts regenerate.
PUSHENVACC landed as `3e32ee0` with the full gate passing. There are now 80
conditional represented opcode bridges. Next: operand-driven PUSH prefixes,
using write-log preservation of their bytecode operand. Full `ArmSim`,
semantic-domain fixes, entry/halt and the lane exits remain open.

## Fixed PUSHENVACC families

`pushenvacc1_arm`–`pushenvacc4_arm` use the same generated push bridge as
stack selections and constants. Its input register list now comes from segment
metadata as well as its result positions. `FieldSelection.read_payload`
factors the existing loop-head field read; `FieldSelection.word_frame` uses
the landed payload write-log frame to preserve the selected field's unique
word. No separate heap-byte survival proof is assumed or duplicated.

Separate default-limit/24 GiB builds pass for all four families: bodies
1.3–1.5s, represented bridges 1.1–1.3s. ENVACC1, GETVECTITEM and PUSHACC1
regressions pass; the original read API is retained. The fixed PUSHACC/PUSHCONST
landing is `29b05a2`, full gate passing. There are now 77 conditional represented
opcode bridges. Next: PUSH-prefixed closure offsets and variable-operand
prefixes. Full `ArmSim`, the semantic corrections, entry/halt and lane exits
remain open.

## Fixed PUSHACC and PUSHCONST families

`pushacc1_arm`–`pushacc7_arm` and `pushconst0_arm`–`pushconst3_arm` now
share `gen_push_arms.py` with PUSH/PUSHACC0. The generator derives postcondition
register positions from the generated segment metadata. Old stack selections
use `PushWriteOk.stack_read`, preserving their total word through the one-word
push log; constants reuse the existing immediate-value representation.
Each represented proof keeps the intermediate memory opaque through its exact
equation, matching the machine generator's store/load interface.

All eleven families pass separately under 24 GiB/default limits. Machine
bodies are approximately 1.3–1.4s and represented bridges approximately 1.1s.
PUSH/PUSHACC0 regressions pass with the generalized template. The initial
represented push landing is `43905e1`, full gate passing. There are now 73
conditional represented opcode bridges. Static write separation, runtime
window stability and selected-load geometry remain explicit. Next: fixed
environment PUSH loads and other shared PUSH prefixes. Full `ArmSim` and
lane exits remain open.

## Represented PUSH and shared write restoration

`push_arm` and `pushacc0_arm` (`Sim/Push.lean`, `Pushacc0.lean`) are generated
through `gen_push_arms.py`. `PushWriteOk` names stack space, RAM/alignment,
image, payload and primitive-table separation. `push_value_restore` uses
existing write-log frame lemmas, adds the saved accumulator to the represented
stack, retains live roots and restores all loop/platform parts. Its runtime
premise is `WindowStable` for exactly the saved stack word. These static
placement/frame facts remain explicit invariant-adapter obligations.

The common `dispatch_compose` now handles every dispatch/body run concatenation;
`running_of_payload` assembles the final relation for both memory effects.
`StackPost` keeps the exact memory map opaque. `live_stack_of_root` and
`payload_stack_of_root` factor stack-edit root preservation, with POP and
integer-consuming arms retained as specializations. PUSH can return any
already live value through `push_value_arm`, for later PUSH-prefixed variants.

Default-limit/24 GiB builds: stack payload 0.983s, push payload/address 0.941s,
write restoration 1.1s, PUSH bridge 1.0s and PUSHACC0 0.984s. Constant,
arithmetic, POP and vector regressions pass. The generated-store milestone
landed as `b03069c`, full gate passing. There are now 62 conditional represented
opcode bridges. Next: PUSHACC1 and the remaining generated PUSH variants;
full `ArmSim`, semantic gaps, entry/halt and lane exits remain open.

## Generated stack-write machine bodies

`tr_push`, `tr_pushacc0` and `tr_pushacc1` now certify their exact store
effects, local code-pin survival, and register/output frames. The shared
`gen_arm_pilot.py` route handles SD sites and threads each resulting memory
map into later total loads. Generated `*_code_store` certificates preserve
local instruction pins under an explicit disjoint store window.

The segment emitter now accepts an optional named intermediate memory and
its exact defining store equation. The caller can instantiate that equation
with `rfl`; it is not an execution assumption. This keeps expanded map writes
out of subsequent load-expression elaboration. An initial inline-map
PUSHACC1 attempt reached approximately 12 GiB and was stopped. The named-map
version builds in 1.3s at default limits under 24 GiB. PUSH and PUSHACC0 also
pass separately. Full existing arm artifacts regenerate unchanged.

These three are machine bodies only; they do not increase the 60 represented
opcode bridges. Next: shared dispatch composition and payload/stack-write
restoration, using the primitive lane's write-log frames. Closure-offset
bridges landed as `5d6f721` with the full integration gate passing.

## Read-only closure offsets

All four `offsetclosure*_arm` bridges are generated by
`gen_closure_offset_arms.py`: M3, 0, 3 and the signed operand-driven variant.
`ClosureOffset` separates the represented environment pointer, its placement,
and the semantic target equation. `pointer_offset_word` / `signed_index_word`
handle modular pointer arithmetic, while `ClosureOffset.root` retains the same
live allocation. Negative operands are supported when the target offset is
nonnegative. Dispatch/runtime framing and operand geometry remain explicit.

Default-limit/24 GiB checks pass separately: shared offset helper 0.881s;
fixed bodies approximately 1.0s and bridges below 1.1s; variable body 1.3s and
bridge 0.971s. The byte-load landing is `f9b4189`, full gate passing after
adopting concurrent library-summary work. There are 60 conditional represented
opcode bridges. Next: extend the generated machine/frame route to stack writes.
Full `ArmSim`, entry/halt, semantic gaps and the lane exits remain open.

## Byte-indexed string and bytes reads

`getbyteschar_arm` and `getstringchar_arm` are generated by one
`gen_byte_arms.py` template over the shared native nine-instruction shape.
`ByteSelection.read` resolves the represented live bytes object, and
`value_byte_index` / `byte_tag` connect native untagging and unsigned-byte
retagging to the semantic result. The supplied byte RAM window proves the
index is below 2^62; no separate sign assumption is added. `consume_arm`
restores the stack after removing the index.

`stack_integer_word` now factors the repeated top-of-stack observation in
binary, vector and byte-load bridges. The arithmetic generator and GETVECTITEM
consume it. Separate default-limit/24 GiB builds pass: byte-index arithmetic
0.908s; GETBYTESCHAR body 2.4s and bridge 1.1s; GETSTRINGCHAR body 2.5s and
bridge 1.1s; vector and ADDINT regressions pass. Audits/drift checks cover both
new families and the helper. Vector reads landed as `2b92e07`, full gate passing.
There are 56 conditional represented opcode bridges. Next: read-only closure
offsets, then stack-writing families. Full `ArmSim` and lane exits remain open.

## Vector reads through general stack consumption

`getvectitem_arm` (`Sim/Getvectitem.lean`) composes the generated eight-step
body with `FieldSelection.read` and `consume_value_arm`. It consumes the
integer stack index and keeps the selected field live as the new accumulator.
`value_index_word` (`Sim/ValueIndex.lean`) proves native arithmetic untagging
followed by scaling by eight equals the semantic unsigned-index offset
modulo 2^64, for all 63-bit indices. No extra sign premise is required.
Successful field selection and the stack/field RAM read windows are explicit.

24 GiB/default-limit builds: index arithmetic 0.842s; body 2.2s; represented
bridge 1.1s. The POP/general-consumption landing is `57ded25`, with the full
gate passing. There are 54 conditional represented opcode bridges. Next:
byte-indexed string/bytes reads; full invariant adapters and `ArmSim` remain open.

## General stack consumption and POP

`ConsumeValuePost`, `consume_value_restore` and `consume_value_arm`
(`Sim/StackConsume.lean`) generalize the integer binary restoration to an
arbitrary represented value. The result becomes a live accumulator root
before source stack slots are dropped. Existing integer APIs are direct
specializations, with no repeated dispatch/run proof.

`pop_arm` and `pop_step_arm` (`Sim/Pop.lean`) consume a bounded nonnegative
operand count and preserve the accumulator. The generated five-step body
and image pins come from `gen_arm_pilot.py`; the semantic adapter derives
the stack bound from the actual `stepI` result. Operand sign, code read
geometry and runtime stability remain explicit premises.

Default-limit/24 GiB checks: generalized restoration 0.928s; POP body 1.3s;
POP represented and semantic bridge 1.0s. ADDINT regression passes through
the integer specialization. The indexed-load landing is `26bdddf`, with
all integration gates passing. There are now 53 conditional represented
opcode bridges; complete `ArmSim`, entry/halt and the lane exits remain open.
Next: consume a vector-index slot using the general value-result restoration.

## Indexed stack and field loads

`acc_arm`, `envacc_arm` and `getfield_arm` (`Sim/Acc.lean`,
`Envacc.lean`, `Getfield.lean`) connect the generic operand-indexed bodies
to represented values. One `gen_indexed_arms.py` template handles all three,
using `index_word`, `FieldSelection.read`, `stack_value_root` and `accu_arm`.
Each requires an ordinary operand read, a nonnegative index, a successful
selection and RAM/HTIF read geometry. These are explicit adapter obligations,
not consequences currently claimed from `Running`.

Separate 24 GiB/default-limit builds pass: ACC bridge 1.1s; ENVACC body
1.5s and bridge 1.1s; GETFIELD body 1.6s and bridge 1.2s. Audits and drift
checks include the new families. The preceding atom/AUIPC landing is
`05312d5`, with the full gate passing. There are now 52 conditional represented
opcode bridges. Next: stack-changing arms and their shared frame/restoration.
Full `ArmSim`, entry/halt, semantic-domain corrections and the lane exits
remain open.

## Atom arms and a negative-index semantic gap

`atom0_arm` and `atom_arm` (`Sim/Atom0.lean`, `Atom.lean`) are generated
through `gen_atom_arms.py`, using the corrected runtime table binding.
The table's global load geometry and AUIPC-relative effective address are
proved from `Layout.sym_caml_atom_table`. `atom_word_of_binding` and the
existing live-root restoration complete both bridges. The parameterized
arm additionally takes an ordinary operand read and a nonnegative index.

`atom_negative_index_obstruction` (`IndexWord.lean`) checks why that last
premise cannot silently be dropped: ATOM's operand -1 gives a native offset
of zero from the allocated table, whereas the current `Int.toNat` semantic
conversion chooses atom 0, one word later. This is a word-level witness,
not a complete Loaded/Sail counterexample. A2-sem needs to address this
operand domain; the headline has not gained an exclusion premise.
`index_word` factors the valid nonnegative scaling for later indexed arms.

The shared ALU descriptor now handles AUIPC and LUI via the existing
`execute_utype_*_char` theorems. Site and segment generators agree on the
actual instruction PC, with no GPR source invented for upper immediates.
Five generator tests pass, and all 18 ALU classes have kernel-checked ELF
smoke sites. Default-limit, 24 GiB builds: ALU sites 1.2s; ATOM0 body 1.3s
and represented bridge 1.0s; ATOM body 1.0s and bridge 1.1s. The atom-table repair landed as `89571a8` with
the full gate passing. There are now 49 conditional represented opcode
bridges; entry, complete `ArmSim.next`, halt and the semantic gaps remain open.

## Atom-table representation repair

The pinned ATOM0/ATOM bodies load the pointer stored at `caml_atom_table`.
The old `valWord (.atom t)` instead added the tag offset to the address of
that global variable. The checked whileMin store log has global address
`0x800649a0` and table pointer `0x8038c000`. `captured_atom_not_legacy`
(`Sim/AtomObstruction.lean`) proves the native ATOM0 result word differs
from the legacy value, under the existing certified memory projection.
This is a word-level witness, not a claimed whole-program execution.

`Place.atomBase` now names the allocated static table. `LoadedAt`,
`VmReprAt` and `VmPayload` bind it to the total runtime word at
`Layout.sym_caml_atom_table`. `atom_word_of_binding` connects this field to
native atom-pointer arithmetic. `gen_boot_heap.py` derives the base and its
read certificate from the captured store log; the existing boot `loaded`
assembly consumes the certificate. `OcamlrunRefinement` is unchanged
(byte-compared), and no semantic rule is changed.

The base stays fixed under heap relocation. `Eqv.atAtoms` / `atomBaseEqv`
add only a fixed global-word image to `VmImage`; `vmReprAt_reloc` transports
it. Read-only framing preserves the binding, and write-log framing adds
`PayloadOutside.atomBase` for a1-prims' mutating summaries. `EvenPlace.atoms`
states the atom-table alignment needed by ISINT and Boolean tests, replacing
the accidental proof that the pointer-global address was even.

Targeted core/relocation/frame checks and the boot Loaded assembly pass
under 24 GiB at default limits. ATOM arms will follow this contract repair.
Immediate-comparison branches landed as `47d9f5c` with the full gate passing;
47 represented opcode bridges remain conditional, and full `ArmSim` is open.

## OFFSETINT width correction needed in a2-sem

The pinned OFFSETINT body uses `slliw` at `0x8000324c`: the operand is
shifted in 32 bits and then sign-extended to 64. `stepI` currently shifts
`BitVec.ofInt 64 n` in 64 bits. For operand `0x40000000` and accumulator 64,
these produce different represented integers. `offsetint_width_obstruction`
(`OCaml/Vm/Sim/OffsetWidth.lean`) kernel-checks that difference using the
exact Sail operand expression from the generated `tr_offsetint` postcondition.
The five-step machine body and ELF-image projection are proved. This is a
word-level obstruction, not a complete `Loaded`/Sail whole-program result.

Reproduce: `python3 scripts/probe_offset_width.py --expect-model 1`.
It compiles a Stdlib-free OCaml 4.14.4 program testing `size () + 1 > 0`,
then changes only OFFSETINT's operand to `2^30`. Baseline host/runbc exit 1;
patched host exits 2 while runbc exits 1. The script reads opcode numbers
from `gen_opcodes.opcodes`, and supports `--expect-model 2` to validate the
repair. No assumption excluding the operand was added to the headline.

A2-sem must match the pinned 32-bit shift for OFFSETINT. OFFSETREF has the
same 64-bit expression in `stepI` and `slliw` at `0x80003230`, so needs the
same width correction; its complete store arm is not proved here. The
arithmetic obstruction is independent of `stepI`, allowing it to remain as
regression documentation after the fix. Other arm families remain unblocked.

Default-limit 24 GiB checks: OFFSETINT body/pins 5.56s (segment 2.1s),
arithmetic witness 3.60s (module 2.3s), peak process RSS below 2 GiB.
CONSTINT landed as `9786220` with the full gate passing.

## Immediate integer comparison branches

`gen_compare_branch_arms.py` emits both paths and the successful-step wrappers
for BLTINT, BLEINT, BGTINT, BGEINT, BULTINT and BUGEINT. `longVal_native`
(`BranchCompare.lean`) proves exact 64-bit arithmetic untagging, and
`compare_code_word` reuses the signed relative-address law at operand 2.
`brOp_accu` extracts the integer accumulator from semantic success. Native
guards reuse `ComparisonArithmetic` and all restoration goes through
`control_arm`; no new run algebra or per-site execution proof is introduced.

Both operands use `OperandAt.read32`; the fallthrough path reads only the
comparison operand and does not assume a successful relative target. The
full-step wrapper carries both read geometries explicitly. The accumulator,
VM payload, primitive bindings and complete platform state are preserved.

Families build separately under 24 GiB at default limits. BLTINT's jump
body takes 2.9s and its represented proof 1.2s; fallthrough body 1.3s,
represented proof 1.1s, and composition 0.98s. There are now 47 conditional
represented opcode bridges. Stack comparisons landed as `d0de539` with the
full gate passing. Entry, full `ArmSim.next` and halt remain open; the
OFFSETINT/REF semantic width correction is still needed from a2-sem.

## Signed and unsigned integer comparisons

The `*_step_arm` theorems for LTINT, LEINT, GTINT, GEINT, ULTINT and UGEINT
(`OCaml/Vm/Sim/*int.lean`) cover both native paths of each successful
semantic step. `ComparisonArithmetic.lean` supplies four shared native
signed/unsigned guard identities and `cmpOp_next` extracts represented
integer inputs from a successful semantic comparison. These proofs compare
the actual tagged words, exactly as `stepI` does.

The existing binary generator now emits guarded comparison paths and their
composition. It reuses the same stack consumption, payload/root restoration,
load observations and generated register assignment as arithmetic and shifts.
The arm generator follows each physical branch to its false-result helper
or true-result fallthrough, preserving the guard in the machine contract.

All six families are checked separately under 24 GiB at default limits.
LTINT's represented paths take 1.1s each and composition 0.84s after the
machine bodies. There are now 41 conditional represented opcode bridges;
dispatch readiness, runtime memory frame and stack-read geometry remain
explicit. Integer shifts landed as `16c3654` with the full gate passing.
Full `ArmSim` and its entry/halt fields remain open.

## Integer shifts

`lslint_step_arm`, `lsrint_step_arm`, and `asrint_step_arm`
(`OCaml/Vm/Sim/Lslint.lean`, `Lsrint.lean`, `Asrint.lean`) extend the existing
binary-arm generator and stack-restoration proof. `shift_count`
(`ShiftArithmetic.lean`) connects Sail's low-six-bit extraction after
arithmetic untagging to `n.toNat % 64`, for every 63-bit input. Its three
native shift adapters and `left_shift_odd` discharge the complete machine
result/tagging expressions; no restricted shift-count domain is assumed.

Bodies and represented bridges build separately under 24 GiB at default
limits. LSLINT takes 2.1s for the body and 1.1s for the represented bridge;
LSRINT/ASRINT bodies take 1.9s and bridges take 1.2s/1.1s. The shared
arithmetic module takes 0.85s. There are now 35 conditional
represented opcode bridges. The five binary arms landed as `0434121` with
the full gate passing. Entry, full `ArmSim.next`, halt, and the OFFSETINT
width correction remain open.

## Read-only stack-consuming arithmetic

`gen_binary_arms.py` emits ADDINT, SUBINT, ANDINT, ORINT and XORINT bridges,
including `*_step_arm` wrappers consuming a successful `stepI` result.
`intOp_next` (`BinarySemantics.lean`) extracts the two represented integer
inputs and remaining stack once for the family. `tag_add` and the existing
`tag_sub` establish the modular arithmetic; `tag_untag_odd` establishes the
shared tag/untag round trip for all odd native bitwise results.

`stack_drop`, `live_stack_drop`, and `payload_stack_drop` (`StackDrop.lean`)
transport stack shape and live-root observations after consuming a prefix.
`consume_arm`/`consume_restore` (`StackConsume.lean`) compose dispatch and
restore the result. `readOnly_restore` (`ReadOnly.lean`) now shares the
platform/image/primitive-binding frame with the earlier accumulator-only
restoration. No new invariant field or headline premise is introduced.
The generated bridges derive stack non-wraparound from representation;
RAM/HTIF geometry and dispatch/runtime-frame premises remain explicit.

All five machine bodies and represented bridges pass separate builds under
24 GiB at default limits. New bodies take 1.0–2.1s; represented bridges take
1.2–1.7s, after the common helpers are cached. The generator reads pin order
and native result expressions from the generated segment JSON, avoiding a
second hand-maintained register assignment. There are now 32 conditional
represented opcode bridges. Conditional branches landed as `54450e7` with
the full gate passing; full `ArmSim`, entry and halt remain open.

## Conditional branches

`branchif_arm` and `branchifnot_arm` (`OCaml/Vm/Sim/Branchif*.lean`)
compose both generated machine paths from a successful `stepI` result.
`false_word_iff` (`IsintArithmetic.lean`) identifies the native false word
using even placement and a non-raw accumulator. These remain explicit
premises, alongside operand/dispatch readiness and the runtime memory frame.
The fallthrough path does not require a successful relative target.

`control_arm` (`Immediate.lean`) shares accumulator/root restoration across
BRANCH and both conditional opcodes. `gen_arm_pilot.py` now walks explicitly
guarded disassembly paths, including branches into shared helper blocks;
dispatch uses the same walker with unchanged generated output.
`gen_conditional_arms.py` generates path bridges and semantic composition,
with drift checking in the full gate. Four machine paths and all four
represented path bridges pass under 24 GiB at default limits. Machine
paths take 3.4–3.9s separately; represented paths take 4.3s each in a combined
build. Semantic composition builds separately in 2.3s/1.5s. There are now 27 conditional represented opcode bridges; full
`ArmSim.next`, entry and halt remain open. BRANCH landed as `e66d024`.

## Signed relative branch

`branch_arm` (`OCaml/Vm/Sim/Branch.lean`) composes the generated four-step
BRANCH body with dispatch, preserving the accumulator, memory and remaining
VM/platform state. `target_int` and `relative_code_word` prove the signed
relative bytecode-to-machine address identity, for forward and backward
branches and arbitrary operand-base offsets. `OperandAt.read32` factors the
read-only prefix observation shared with CONSTINT.

The represented bridge takes successful semantic `target` computation and
the existing ordinary operand/dispatch/runtime-frame premises. Its targeted
build is 1.0s (1.57s wall); the final shared-helper rebuild takes 3.91s, with
peak process RSS below 2 GiB under 24 GiB. CONSTINT rebuilds after adopting
the same operand helper. Fixed environment/field arms landed as `b52357e`
with the full gate passing; BRANCH brings the conditional arm count to 25.

## Fixed environment and field loads

`gen_field_arms.py` emits `envacc1_arm`–`envacc4_arm` and
`getfield0_arm`–`getfield3_arm` over their census-generated total-load bodies.
`field_selection` (`FieldRead.lean`) derives the source pointer and placement
witness from successful abstract lookup plus `HeapRepr`. `FieldSelection.read`
uses a1-prims' `VmPayload.object_at` to recover the selected word and proves
it is an existing live root. Every bridge then uses `accu_arm` to restore the
full data/platform/loop state.

`RamReadAt` (`ReadGeometry.lean`) is the shared natural-address RAM/HTIF
contract and projects to the existing `ReadWindow` interface. `CodeReadAt`
is its four-byte specialization; load addresses and HTIF symbols use `Layout`
or abstract placements. Field geometry is still an explicit premise.
`represented_register` is shared in `ArmInput.lean`; field and unary bridges
reuse its value-uniqueness proof. No `Running` or headline fields are weakened.

All eight families pass separately under 24 GiB at default limits:
ENVACC1–4 6.24/6.56/5.60/5.49s, GETFIELD0–3 6.52/6.16/6.48/5.75s.
Each bridge elaborates in 1.2–1.5s; peak process RSS stays below 2 GiB.
This brings the conditional represented arm count to 24. Unconditional
`ArmSim` entry/next/halt and the machine `whileMin` result remain open.
The OFFSETINT obstruction landed as `3a514fc`; main now includes A0-boot's
`bc63ae6` captured-entry `Loaded` certificate, including primitive bindings.

## Primitive binding repair

The obstruction landed as `2bb35a3`. `primitive_binding_obstruction` now
retains that checked result against the explicit legacy `UnboundLoaded` /
`UnboundRefinement` snapshot. The generated probes have identical code,
heap, globals and world; swapping only word-size/int-size names in PRIM
changes the exit from 64 to 63. Host ocamlrun, runbc, and Lean agree; both
programs are `Good` and fit any budget covering their initial heap. The
obstruction is conditional on a loaded witness, not a concrete boot proof.

Production `LoadedAt` and `VmReprAt` now carry named `PrimitiveBindings`.
It ties every `P.prims` entry to the function pointer read by C_CALL.
`PrimitiveEntries.lookup` is generated from all 403 parallel name/address
entries in the pinned ELF, checked against symbols and `.text`; its balanced
lookup has named facts for all 30 F1 primitives. The table symbol and contents
offset come from `Layout`, with the offset recovered from C_CALL1's load.
`loaded_probes_disjoint` proves the old ambiguity is excluded.

`PrimitiveBindings.frame` preserves the metadata under memory equality;
CONST0/NEGINT’s shared restoration uses it. `primitiveBindingsEqv` uses
`Eqv.all` / `guard` / `observe`; `VmImage.primitives` asks the collector to
preserve the selected function-pointer observations. No abstract heap pointer
is renamed. The existing `vmReprAt_reloc` and GC `LoopHead` consumer build.
A0-boot must supply `LoadedAt.primitives` at the cut. The newly landed
`WhileMinEntry.EntryControl` carries that explicit obligation; its `loaded`
assembly consumes it, and `fillZero` preserves it via `of_words` and the
existing `bytesT_memEqv` law. C_CALL arms can consume
read-only primitive memory frames; mutating summaries will need the metadata
frame as well. Primitive bodies remain a1-prims-owned.

`OcamlrunRefinement` was compared byte-for-byte with the pre-repair definition
and is unchanged. The HTIF obstructions remain checked, with their memory
frame extended to preserve primitive bindings.

Validation: resolver 14s, representation 1.2s, refinement 1.1s, relocation
2.1s, legacy/disambiguation regression 2.8s, GC invariant 1.0s. CONST0 and
NEGINT rebuild at 1.1s / 1.2s; targeted runs remain below 2.08 GiB under
24 GiB. No proof budget changed. Drift, discipline and abstraction checks
pass; the full integration gate passed and landed the repair as `9eeb667`.

## CONSTINT and ordinary operand reads

`constint_arm` (`OCaml/Vm/Sim/Constint.lean`) composes the generated
five-instruction load/tag/advance body with dispatch and full representation
restoration. It returns `.int (BitVec.ofInt 63 w.toInt)` and advances PC by
two, exactly matching the signed bytecode operand. `tag_word32` uses the
existing sign-extension and shift/add laws; no operand values are enumerated.

`OperandAt` names the fetched code word, non-cache position and code RAM
geometry. `code_read`, `CodeReadAt.toNat` and `OperandAt.read` give the common
observation bridge; `ArmInput.of_repr` reuses the same facts. `codePc_add`
generalizes the existing successor address identity. These remain explicit
input facts, not a claim of unconditional `ArmSim.next`.

Default-limit 24 GiB builds pass: body/pins/arithmetic 5.70s; represented
bridge plus shared helpers 5.61s (bridge 1.6s), peak process RSS below 2 GiB.
BOOLNOT landed as `5d473b0` with the full gate passing. CONSTINT brings the
represented conditional arm count to 16.

## Unary tagged subtraction

`gen_unary_arms.py` emits both NEGINT and BOOLNOT represented bridges from
one template over the census-generated four-instruction bodies. `tag_sub`
proves the 63-bit modular subtraction identity once; `tag_neg` and `tag_not`
instantiate it for machine constants 2 and 4. `boolnot_arm` restores the
exact `stepI` result `1 - n` for every integer accumulator, without assuming
it is a Boolean. It retains the existing explicit `ArmInput` / runtime-frame
premises. All new body, image and bridge theorems are audited and generated
artifacts are drift-checked.

BOOLNOT builds in 8.14s (bridge 1.7s), under 2 GiB peak process RSS and the
24 GiB cap. ACC0–ACC7 landed as `32025f5` with the full gate passing; BOOLNOT
brings the represented conditional arm count to 15.

## ACC0–ACC7 representation bridges

`accu_restore` and `accu_arm` (`OCaml/Vm/Sim/Immediate.lean`) generalize the
shared restoration/composition to represented accumulator words. They consume
`VmPayload.accu_of_root` from a1-prims; immediate arms specialize this rule
without a second heap/root proof. `stack_value_root` in `StackAcc.lean` selects an
existing stack root, and `stack_slot_nat` derives non-wrapping addresses from
stack shape and the represented `stack_high` word.

`gen_acc_arms.py` emits `acc0_arm` through `acc7_arm`; the census/site/segment
pipeline emits every machine body and ELF pin. Each bridge selects the exact
abstract stack value, advances PC by one, and restores all data/platform/loop
fields. The only extra load premise is the shared `ReadWindow` RAM/HTIF
geometry; absent bytes remain total zero reads. Dispatch readiness and runtime
memory stability remain explicit, so these are conditional represented arms.

Separate default-limit builds under 24 GiB pass: ACC0 3.96s including shared
restoration, ACC1–ACC7 4.51/4.53/6.66/5.16/5.55/5.60/5.70s. Each generated
bridge elaborates in 1.0–1.4s; peak process RSS remains below 2 GiB. The
14 represented arm bridges are CONST0–3, NEGINT, ISINT and ACC0–7; generic
ACC has its machine body only. The F1 `ArmSim` exit remains open.

## ISINT representation bridge

`isint_arm` (`OCaml/Vm/Sim/Isint.lean`) composes generated dispatch/ISINT
segments through `immediate_arm`. `IsintArithmetic.lean` proves the body's
shift/mask/add result equals `Val.ofBool s.accu.isInt` under `EvenPlace` and
the semantics' non-raw-value condition. `EvenPlace` requires even code and
heap placements; it is an explicit premise, not yet part of `Running`.
`isint_not_valWord` is a checked value-level counterexample: a pointer placed
at address 1 has the same word as integer zero, so `valWord` alone cannot
justify the classification. This is not a full `Running` counterexample.

Landed as `48219ed` with the full gate passing. Both files build at default limits under 24 GiB: arithmetic 1.2s, bridge
1.5s, total wall 3.46s, peak process RSS below 2 GiB. The new theorem names
are included in the axiom audit. The constant-arm family landed with the
full gate as `ebf75db`.

## Constant-arm family

`immediate_arm` (`OCaml/Vm/Sim/Immediate.lean`) composes the shared dispatch
run, any generated immediate-result body, and `immediate_restore` once.
`DispatchPost.image` supplies the body image from dispatch's memory frame.
CONST0 and NEGINT now consume this rule. `gen_const_arms.py` emits represented
CONST0–CONST3 bridges; `gen_arm_pilot.py` emits their machine bodies, sites,
ELF pins and image projections from the census. The new `const1_arm`,
`const2_arm`, and `const3_arm` restore the exact semantic PC/accumulator result
and every data/platform/loop component, including primitive bindings.

These remain conditional on `ArmInput` and `MemoryStable L.runtimeOk`;
no unconditional `ArmSim.next` case is claimed. Axiom and generator-drift
checks cover the new family. Separate default-limit builds under 24 GiB:
CONST0 plus composition 3.52s; CONST1 5.92s, CONST2 4.74s, CONST3 4.58s.
New constant bridge elaboration is 1.0–1.4s; peak process RSS below 2 GiB.

## Earlier core landings

The repair (`ef4e701`), CONST0 (`3229c53`), and ISINT/shared ALU adapter
(`7994562`, integration head `dac2c19`) have landed through
`scripts/integrate.sh`. The delayed integration completed successfully
when host memory recovered; all gates, including the 16 ALU smoke sites,
passed. NEGINT subsequently landed as `e2777bc` with all gates passing.
ACC/ACC0 subsequently landed as `dd48ca0` with all gates passing.
Counted contracts landed as `a22f2b9`; register/console frames as `ee18571`.
Dispatch and checked pin lookup landed as `2857cd0` / `7e2ae1a`, after
a full gate and a rebase over the primitive lane’s signed comparison.
The table facts landed as `c7989c8`, with the full gate passing.
Composed dispatch landed as `fe72ca4` with the full gate passing.
The CONST0 representation bridge landed as `85275ba` with all gates passing.
NEGINT and post-migration checks landed as `c26cecd` / `50aa08d`, with the
full gate passing against the new image.
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

## ELF migration

Rebased onto A0-boot’s `272e436` / `7fa1750` fixed-`.embed` migration.
Pinned ELF SHA-256: `b055163e2280efbec1d16c255afccf31e23315f9f37a7ffcba5bbed0850b1c99`.
Regenerated `gen_ocaml_image.py`, `gen_arm_pilot.py`, `gen_alu_pilot.py`,
and `gen_dispatch_table.py` after the rebase; all outputs agree with the
migrated artifacts. Function addresses remain fixed. Data references use
`Layout`; load-contract RAM bounds remain architectural limits.
The old integration attempt was stopped after its automatic migration rebase
so regeneration preceded further validation. Post-migration checks precede landing the current NEGINT bridge.
All six generated families rebuild successfully at default limits. CONST0’s
full dependency rebuild took 88.61s, peak process RSS 2.52 GiB; NEGINT,
ISINT, ACC0, and ACC then took 2.38–3.48s each, below 2.07 GiB.
The dispatch segment and named boundary each rebuilt in about one second.

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

* `Vsa.Sim.PinsHold.get` (`Vsa/Sim/PinLookup.lean:10`) is the shared
  finite-index accessor for register-pin lists. The segment generator uses
  it for pin reads and bundle restriction, eliminating deep positional
  conjunction projections. Its index bound simplifies only list lengths.
  Dispatch's first full gate exposed the old generator's positional
  projections; this fixes the generator without a discipline exemption.

* `Vsa.Sim.tr_dispatch` (`OCaml/Vm/Sim/DispatchSegment.lean:22`) proves
  the in-range eight-step loop-head path: opcode load, bound branch,
  jump-table offset load, and indirect jump. It exports `TripleN 8`, memory
  equality and `StepFrameOut`. `dispatch_loaded` supplies instruction pins.
  The path starts at the census loop head and follows the decoded taken
  branch; no data symbol is hard-coded. RAM/HTIF bounds, opcode guard, and
  target alignment remain explicit. A bridge from Running and the pinned
  jump table to these conditions and the selected arm address is still open.
* The shared segment front end now names branch site variants consistently
  with `gen_sites.py`; indirect-jump output can retain the exact machine
  target expression without an unnecessary rewrite premise.

* The shared generator now exports a `StepFrameOut` component for every
  pilot body, through its optional `frame_origin` parameter. The caller
  supplies the incoming state; the post preserves console output and all
  registers outside the computed write log. One `chain_frame_out` fold
  consumes the generated observations. Memory equality and `TripleN`
  counts remain in the same contract. This uses the existing frame
  abstraction rather than per-site, per-register proof threading.

* The five generated body theorems now return the existing `TripleN`
  instead of forgetting their step counts: CONST0/NEGINT/ISINT/ACC0/ACC
  have lower bounds 3/4/5/3/6. `TripleN.toTriple` retains ordinary triple
  use. The shared generator's optional `counted` mode uses
  `Steps.toN_of_stepsEq` from `Vsa.Sim.StepCount` (the run-kernel counter
  law), not a second induction on machine runs. Calls/custom postconditions
  remain outside this mode; the existing SegSt restriction checks that.

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
  runtime frame and data bridge; no `ArmSim.next` case is claimed.
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
  dispatch-to-body composition, runtime preservation, and the VM-data bridge remain.
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

## Dispatch table

`dispatchOffset_loaded` derives all 149 opcode table words from
`ExecutableImage.rodata`; `dispatchOffset_target` checks their signed offsets
against census targets. `dispatchOpcode_guard`, `dispatchTarget_aligned`, and
`dispatchTarget_clear` check the branch bound and indirect-jump geometry.
All are generated in `OCaml/Vm/Sim/DispatchTable.lean` and its seven chunks
by `scripts/gen_dispatch_table.py`, with data addresses from `Layout.jumpTable`.
Each literal byte is checked separately in the kernel; the full image is
never evaluated as one proposition. `dispatch_run` (`OCaml/Vm/Sim/Dispatch.lean:37`) composes the table with
`tr_dispatch`: from named `DispatchInput`, it reaches the selected arm in at
least eight machine steps. `DispatchPost` records its PC, advanced bytecode
pointer, unchanged memory, and complete frame outside x15/x23 and standard
step noise. `dispatchIndex*` discharge the table RAM/HTIF geometry.
The input retains explicit bytecode-address bounds/HTIF exclusion and tick
bounds, which `Running` does not yet supply; a full arm case is not claimed.

## CONST0 representation bridge

`const0_arm` (`OCaml/Vm/Sim/Const0.lean:14`) composes `dispatch_run` and
`tr_const0` through `StepsN.append`, then restores `Running` for the state
with PC advanced by one and accumulator zero. The payload uses the primitive
lane’s `VmPayload.accu_int` and `.frame`; complete register frames preserve
sp/env/extra and all fixed loop registers. `MemoryStable L.runtimeOk` supplies
the runtime frame, just as it does for the primitive summaries.

`ArmInput` (`OCaml/Vm/Sim/ArmInput.lean:11`) is a named, stronger entry;
`ArmInput.running` projects to `Running`. `ArmInput.of_repr` derives it from
`VmReprAt`, platform/loop facts, the fetched opcode, `CodeReadAt`, tick < 2,
and a non-cache opcode position (`methodCacheSlot ... = false`). The last
condition is needed because the landed F3 `CodeRepr` permits cache words to
vary. These remaining premises are explicit; neither `ArmSim.next` nor the
headline refinement is claimed or weakened.

## Shared immediate arms and NEGINT

`immediate_restore` and `immediate_preserved` in
`OCaml/Vm/Sim/Immediate.lean` package the restoration of VM data, fixed
registers, executable image and runtime from an `ImmediatePost`. CONST0 now
uses this shared rule. `negint_arm` (`OCaml/Vm/Sim/Negint.lean:12`) composes
its generated dispatch/body with the same rule, returning exactly the
`stepI` accumulator `untag (2 - tag64 n)`.

`tag_neg`, `untag_tag`, and `untag_neg` in `ImmediateArithmetic.lean` prove
modular negation and signed untagging for every 63-bit value. They reuse
`Primitives.tag_toNat`; no bounded-integer approximation or increased proof
limit is involved. Both arm bridges retain the documented `ArmInput` and
`MemoryStable` premises.

## Validation

* Shared restoration and refactored CONST0: 0.931s / 0.962s; 2.49s wall,
  1.96 GiB peak RSS. NEGINT arithmetic / arm: 0.952s / 1.0s; 2.58s wall,
  1.96 GiB peak RSS. Builds are separate and capped at 24 GiB.

* CONST0 representation bridge passes at default limits: ArmInput 1.0s,
  Const0 1.1s, combined 2.72s wall and 1.95 GiB peak RSS, under 24 GiB.

* Composed dispatch builds in 1.4s (2.29s wall, 1.93 GiB peak RSS).
  The extended table chunks build in 1.6–3.5s each, below 1.85 GiB.
  Generator headers disable implicit undeclared identifiers; literal index
  facts are checked separately and composed by opcode cases.

* Dispatch table chunks pass separately under 24 GiB at default limits:
  8.4s, 4.4s, 6.4s, 5.2s, 4.0s, 4.5s, 2.8s; peak process RSS below 1.86 GiB.
  Aggregate target lemmas build in 1.9s (2.68s wall, 1.82 GiB peak RSS).
  Generator drift, discipline, and abstraction checks pass.

* All six segment families pass after the pin-lookup change, each built
  separately under 24 GiB: CONST0 15s, NEGINT 15s, ISINT 6.6s, ACC0 13s,
  ACC 23s, dispatch 11s (shared-host wall timings). Peak process RSS stays
  below 1.86 GiB. Discipline, generator drift, and abstraction checks pass.

* Dispatch build passes under 24 GiB and default proof limits: code 3.7s,
  sites 9.6s, image projection 2.4s, segment 44s; wall 66.55s, measured
  user/system CPU 6.49/2.11s, peak process RSS 1.85 GiB. Shared-host
  scheduling affects these wall timings; no budget was increased.

* Framed body rebuilds, separately under 24 GiB, pass at default limits:
  CONST0 1.6s, NEGINT 2.0s, ISINT 2.5s, ACC0 1.0s, ACC 2.4s.
  Wall times 2.37–3.55s; maximum process RSS 1.85 GiB.

* Counted body rebuilds, one family per build under 24 GiB, all pass:
  CONST0 1.1s, NEGINT 1.2s, ISINT 1.4s, ACC0 1.3s, ACC 1.5s.
  Wall times 1.68–2.19s; maximum process RSS 1.85 GiB. Generator drift
  checks pass; no elaboration limit increased.

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

## OFFSETREF represented heap update

`HeapPayload.lean:27` (`payload_heap_frame`) separates non-heap copying from
heap reconstruction; `payload_field_written` combines it with the landed
heap graph/write proof. `FieldRestore.lean:20` (`field_restore`) restores
unit, registers, image, bindings and runtime after one field store.
`Offsetref.lean:13` (`offsetref_arm`) composes dispatch and the generated
eight-instruction body, including the 32-bit SLLIW contribution and exact
readback. `offsetref_step_arm` matches the real bytecode rule.
All three new modules check (0.8–1.1 s); their headlines enter the axiom audit.
The named `FieldWriteOk` and runtime-window premises remain invariant work.

## Generated trap bodies

`tr_poptrap` follows the no-pending branch (13 instructions), and
`tr_pushtrap` proves the complete 23-instruction body. Both come from
`gen_arm_pilot.py` with opaque, exact load equations, store frames and
full-image pin projections. Measured body builds: 1.9 s and 6.4 s.
Their register/memory observations are machine results; represented
trap-pointer and stack restoration is next. OFFSETREF landed as `25abf35`
with the complete gate passing.

## POPTRAP represented restoration

`PayloadRestore.lean:23` (`payload_rebuild`) now frames common code/world
observations while accepting independently restored stack, heap and trap
components. OFFSETREF reuses it through `payload_heap_frame` unchanged.
`TrapPayload.lean:22` (`payload_trap_written`) reads back the native trap
pointer; `trap_restore` combines that with stack consumption and platform
restoration. `TrapArithmetic.lean:23` (`poptrap_link`) derives the absolute
pointer from the bounded tagged link, using shared `nat_shift_word`.
`Poptrap.lean:13` (`poptrap_arm`) and `poptrap_step_arm` compose the generated
no-pending body with those facts. The bridge checks in 1.2 s; no pending work,
read/store geometry, separation and runtime-window preservation remain named
premises. Generated trap bodies landed as `7c7db48`, all gates passing.

## PUSHTRAP restoration facts

`PushtrapArithmetic.lean:23` proves native relative-link arithmetic with
explicit bounded stack/trap depth. `PushtrapStore.lean:23` proves all five
store readbacks, plus the frame-root fact and named geometry/separation.
`PushtrapRestore.lean:8` (`pushtrap_payload`) joins the four-word frame and
new trap depth; `pushtrap_restore` restores the platform and registers from
the exact log. These modules check in 0.9–1.0 s. The generated-body
composition is next. POPTRAP landed as `0a91a6e`, all gates passing.

## PUSHTRAP represented arm

`Pushtrap.lean:13` (`pushtrap_arm`) composes dispatch, the generated
23-instruction body and `pushtrap_restore`. Both domain loads and the old
trap read after partial writes are justified by sub-log separation.
`pushtrap_step_arm` matches the actual bytecode transition. The bridge checks
in 1.5 s. Its register avoidance certificate splits append/cons membership
before kernel reduction, avoiding a recursion-limit bump. Stack depth,
trap bound, geometry, separation and runtime-window preservation remain
explicit. Restoration facts landed as `63fea79`, all gates passing.

## APPLY represented entry

`Apply.lean:16` (`apply_arm`) and `apply_step_arm` prove the general APPLY
path through its shared stack-capacity and no-pending checks. The generated
10-instruction body checks in 1.9 s; the represented bridge in 1.2 s.
`EnterReady` names capacity, threshold read geometry and no pending work.
`ApplyArithmetic.lean:20` proves the positive 32-bit arity decrement.
`RootFrame.lean` shares heap restriction for environment and stack root edits;
`SignalCheckReady.read32/read` now supply all quiet-flag loads. No premise
claims a machine postcondition. Full invariant derivation and stack-growth
execution remain open. PUSHTRAP landed as `ae89b00`, all gates passing.

## RETURN represented paths

`ReturnMore.lean:16` and `ReturnFrame.lean:15` prove both native paths;
`Return.lean` matches their successful bytecode steps. The generated
eight/ten-instruction bodies check in 1.5/1.8 s, represented bridges in
1.0/1.1 s and wrappers in 0.9 s. `ReturnPayload.lean:10` retains the restored
environment as a heap root before dropping stack words. `ReturnRead.lean:18`
extracts the three saved caller words and its environment root. Operand
nonnegativity, extra-count signed bounds, read geometry and runtime framing
remain explicit invariant premises. APPLY landed as `e33689e`, all gates passing.

## Fixed-arity application bodies and prefix replacement

Generated `tr_apply1`, `tr_apply2`, `tr_apply3` include their shared
no-growth/no-pending tails (17/18/21 instructions), with exact opaque loads,
write frames and full-image pins. Separate body builds take 3.4/3.9/4.7 s.
`LogWindow.lean` derives range separation from a write-window certificate;
`FrameInsert.lean:13` (`payload_replace_prefix`) shares prefix replacement
and untouched-tail/root preservation for application and tail-call frames.
Represented fixed-arity composition is next. Both RETURN paths landed as
`e055960`, all gates passing.

## Shared fixed-arity frame payload

`IndexedStores.lean:23` proves word readback for any store order with unique
indices. `ApplyFrameLog.lean` certifies the three concrete native orders,
coverage and footprint. `ValueWords.lean` shares list/stack-prefix word
representation. `ApplyFramePayload.lean:25` (`apply_frame_payload`) restores
all three application frames via those certificates and prefix replacement;
its target checks in 0.9 s. Fixed-arity native bodies landed as `03a1343`
with all gates passing. Full represented compositions remain next.

## Fixed-arity represented applications

`Apply1.lean`, `Apply2.lean`, `Apply3.lean` now prove `apply1_arm`,
`apply2_arm`, `apply3_arm` and their `*_step_arm` wrappers through the
generated bodies. A single `scripts/gen_apply_fixed.py` reads segment order
and register pins; shared frame restoration supplies `Running`. APPLY1/2
adapters check in 1.8/2.1 s. The frame writes preserve closure, domain,
threshold and pending reads, including APPLY2’s early domain load.
Geometry, stack capacity, no-pending and runtime preservation remain named
premises. Shared restoration landed as `5c5ea6e`, all gates passing.

## Tail-call bodies and shared restoration

`tr_appterm1`, `tr_appterm2`, `tr_appterm3` cover argument moves and the
shared no-growth/no-pending tail (14/16/19 instructions). Their generated
bodies check in 2.9/3.8/4.5 s. `ValueLog.lean` certifies arbitrary contiguous
word-copy readbacks and `payload_copy_prefix`; `TailcallRestore.lean`
assembles the copied stack, closure environment and platform into `Running`.
`TailcallArithmetic.lean` connects scaled slot subtraction and extra-argument
addition to natural counters. Represented native-body adapters are next.
APPLY1–3 landed as `cc62241`, all gates passing.

## Fixed-arity represented tail calls

`Appterm1.lean`, `Appterm2.lean`, `Appterm3.lean` prove `appterm1_arm`,
`appterm2_arm`, `appterm3_arm` and their `*_step_arm` wrappers. One
`scripts/gen_tailcall_fixed.py` reads segment order/pins and supplies checked
word moves to `tailcall_restore`. Copy footprints, operand nonnegativity,
stack capacity and runtime preservation remain explicit. Tail-call bodies
and shared restoration landed as `76fa626`, all gates passing. Next are GRAB allocation,
RESTART, the generic tail-call loop and allocation/barrier-backed families.

## GRAB satisfied-arity path

`GrabFast.lean:15` (`grab_fast_arm`, `grab_fast_step_arm`) composes the
six-instruction generated path when enough arguments are present; its bridge
checks in 1.0 s. `GrabArithmetic.lean` proves the signed guard and natural
subtraction. The shared `IndexWord.nonnegative_word32` now also supplies
indexed loads and C_CALLN. Operand nonnegativity, bounded extra count and
runtime framing remain explicit; GRAB partial-application allocation is open.
Fixed-arity tail calls landed as `bdedeb8`, all gates passing.

## Generic tail-call loop cuts and memory invariant

Generated `tr_appterm_prefix`, `tr_appterm_copy_more`,
`tr_appterm_copy_last`, `tr_appterm_suffix` check in 2.3/1.3/1.3/1.9 s.
The new explicit text cuts in `gen_arm_pilot.py` stop at loop boundaries.
`ReverseCopyLog.lean` proves one-store extension, empty initial log, final
represented readbacks, suffix footprint and unread-source preservation even
when destination/source overlap. `ValueWords.readback` now shares the slot
proof used by APPLY frames and both copy directions. Counted loop execution
through `loopFromBody`, then prefix/suffix composition, is next.
GRAB’s satisfied-arity path landed as `41a698a`, all gates passing.

## Counted backward-copy machine loop

`BackwardCopy.lean` (`backward_copy_run`) proves the actual APPTERM loop for every
31-bit bounded word count, including overlapping ranges. It folds the two
generated branch adapters with `loopFromBody`; there is no assumed iteration
premise. `BackwardCopyState.lean` supplies the cursor-derived measure,
exact log invariant, image preservation and register frame. Counter and cursor
arithmetic share `BackwardCopyArithmetic.lean`; `low32_nat` also simplifies
APPLY’s operand arithmetic. Full represented prefix/loop/suffix composition
is next. Loop cuts and log certificates landed as `039539b`, all gates passing.

## Generic represented APPTERM

`Appterm.lean:10` (`appterm_arm`, `appterm_step_arm`) composes the generated
prefix, proved arbitrary-length backward-copy loop and closure-entry suffix.
The final bridge checks in 0.85 s; setup in 1.0 s. `ApptermInput.lean` names
concrete access/separation requirements, and `TailcallPostWith` plus
`tailcall_restore_of_log` support either copy order. Fixed-arity tail-call
adapters recheck against the generalized restoration. No copy-loop premise
remains. Capacity, geometry and runtime framing are still explicit.
The counted copy loop landed as `e7fe774`, all gates passing.

## RESTART cuts and represented closure fields

Generated RESTART prefix paths, copy-loop branches and suffix are checked
(9/9/7/7/4 instructions). `BlockRead.lean` supplies ordinary block headers,
represented field suffixes and their live roots. `RestartRestore.lean:40`
(`restart_restore`) installs saved arguments, recovers the captured environment
and restores data/platform; it checks in 0.93 s. The counted forward-copy
loop and represented native composition are next. Generic APPTERM landed
as `47c7779`, all gates passing.

## RESTART counted forward-copy loop

`ForwardCopy.lean` (`forward_copy_run`) proves the actual RESTART field-copy
loop for every bounded saved-argument count, with no iteration or execution
premise. `ForwardCopyState.lean` tracks the counter, source snapshot, register
frame and prefix write log. `gen_forward_copy.py` instantiates the continuing
and final generated seven-instruction branches, with drift checks in stage a5.
The whole loop target builds successfully. The native cuts and represented
restoration landed as `7fabf12`, all gates passing.

## Complete represented RESTART

`Restart.lean:12` (`restart_arm`) and `restart_step_arm` compose dispatch,
both generated setup paths, `forward_copy_run` and the generated suffix into
`Running` for the successful RESTART rule. The complete bridge checks in
0.82 s; the setup adapters check in 1.1/1.2 s. `RestartInput.copy_region`
derives source-read separation from live heap-object separation; it does not
assume loop execution. `EnterFrame.root_field_load` shares read preservation
between application accumulators and RESTART environments. Stack capacity,
access geometry, field-count bounds and runtime framing remain explicit.
The counted forward-copy loop landed as `09c960b`, all gates passing.

## GRAB allocation cuts and restoration

The insufficient-arity nursery path now has generated reservation, initialization,
copy-loop branches and caller-frame suffixes (16/16/5/5/11 instructions). Native
segments check in 3.3/3.8/1.1/1.1/2.1 s. `BlockAllocation.lean` shares header
encoding, exact initializer-log layout and captured-root reasoning for ordinary
blocks. `GrabRestore.lean` (`grab_restore`) extends the live heap and restores
the saved caller through the existing allocation and RETURN payload rules;
it checks in 0.89 s. Native loop composition and nursery-side conditions remain
open. Full represented RESTART landed as `8eb35e2`, all gates passing.

## GRAB counted source-cursor copy

`CursorCopy.lean` (`cursor_copy_run`) proves the actual GRAB copy loop for
arbitrary bounded argument lists from its two generated five-instruction
branches. `OCaml/Run/CountedLoop.lean` shares the termination fold with RESTART;
`CopyLogFrame.lean` shares prefix-memory and image preservation. One generator,
`gen_forward_copy.py`, now instantiates both field-indexed and pointer-cursor
copy branches. The loop checks in 0.77 s, and full RESTART rechecks in 0.83 s.
GRAB cuts and restoration landed as `f447142`, all gates passing. Remaining
GRAB work is the nursery prefix, initializer/copy composition and caller suffix.

## GRAB nursery reservation and partial-closure layout

`GrabReserve.lean` (`grab_reserve`) composes the actual allocating prefix
through its nursery reservation from named scalar G1 capacity/geometry
conditions; it checks in 1.1 s. Generated `GrabAllocPrefixLayout` and
`GrabAllocInitLayout` resolve ELF-relative globals through `Layout`.
`ClosureLayout.lean` (`partial_closure_layout`) checks the real environment,
argument-copy, code and arity store order without commuting memory maps;
it checks in 0.98 s. `value_log_framed` shares readback through surrounding
writes. Initializer/copy/suffix composition remains open. The full counted
GRAB loop landed as `1e64eb6`, all gates passing.

## GRAB initialized copy entry

`GrabInitialize.lean` (`grab_initialize`) composes the generated initializer
with the proved nursery reservation: the header and environment are stored,
the allocated value is installed, and the complete source-cursor copy input
is established. It checks in 1.2 s. `GrabInitInput.copy_after` transports the
original stack snapshot through the actual setup log. Reservation and closure
layout landed as `391b2ca`, all gates passing. The remaining allocating GRAB
composition is its generated caller-frame suffix and the successful-step wrapper.

## Complete allocating GRAB

`GrabAlloc.lean` (`grab_alloc_arm`, `grab_alloc_step_arm`) now composes the
actual dispatch, nursery reservation, closure initializer, arbitrary-count
copy and generated caller-return suffix. `GrabFinish.lean` obtains saved-frame
reads from the allocation payload-separation contract and supplies closure
layout from the completed exact write log. The suffix checks in 1.3 s, and
the whole bridge in 0.85 s. Together with `grab_fast_step_arm`, both GRAB paths
are proved conditionally on machine-input/G1 conditions; no loop execution
premise remains. Nursery/runtime preservation, geometry, placement and the
saved-extra sign bound remain explicit. Initialization landed as `a58e5d5`,
all gates passing. The opcode bridge count stays 121 because GRAB's fast path
was already counted.

## Fixed-arity MAKEBLOCK nursery foundations

Generated MAKEBLOCK1/2/3 nursery bodies (20/24/26 instructions) check in
3.0/5.7/6.7 s. Their generated global-address projections resolve both
ELF-relative references through `Layout`. `MakeblockRestore.lean`
(`makeblock_restore`) shares exact initialized block layout, allocation-root
extension, stack consumption and platform restoration across all arities.
`MakeblockArithmetic.lean` shares bounded tag decoding and header encoding.
The represented native adapters are next. Complete allocating GRAB landed
as `b6ca7b9`, all gates passing.

## Represented fixed-arity MAKEBLOCK arms

`Makeblock1.lean`, `Makeblock2.lean`, and `Makeblock3.lean`
(`makeblock1_arm` / `makeblock1_step_arm`, and corresponding arities)
compose the generated nursery bodies with shared block restoration. They
check in 1.7/2.2/2.7 s. `gen_makeblock_fixed.py` generates all three adapters;
`MakeblockInput.lean` names capacity, geometry, source separation and allocation
conditions. Runtime preservation, placement and signed tag bounds remain
explicit. There are now 124 conditional represented opcode bridges.
The native bodies and shared restoration landed as `c367baf`, all gates passing.
Next: generic MAKEBLOCK, sharing the cursor-copy invariant and proof with GRAB.

## Generic MAKEBLOCK copy loop

`CursorCopyAtPc` and `cursor_copy_run_of_branches` share the pointer-loop
invariant, memory restoration and termination fold across GRAB and MAKEBLOCK.
`MakeblockCopy.lean` (`makeblock_copy_run`) consumes its actual generated
five-instruction branches; each native branch checks in 1.1 s and each adapter
in 0.9 s. GRAB's complete allocating bridge rebuilds successfully against the
shared abstraction. No copy-execution premise remains. Generic MAKEBLOCK still
needs its reservation/initialization and suffix composition. Fixed-arity arms
landed as `96fe151`, all gates passing.

## Generic MAKEBLOCK nursery cuts

Generated reservation (17 instructions), multi-field initialization (16),
single-field initialization (12), and both return suffixes now check.
Reservation checks in 3.5 s, initializers in 3.4/2.1 s and suffixes in
1.1/0.95 s. Their global-address projections use `Layout`. The represented
reservation and initialization adapters are next. The actual arbitrary-count
copy loop landed as `94b214f`, all gates passing.

## Represented generic MAKEBLOCK reservation

`MakeblockReserve.lean:14` (`makeblock_reserve`) decodes both operands,
checks the nursery-size/capacity guards and establishes `MakeblockReserved`
from the actual generated prefix. It checks in 1.1 s. `MakeblockLog.lean`
(`value_log_cons`, `makeblock_log_parts`) joins the setup stores and arbitrary
field copy into the canonical allocation log. `CursorCopyRegion.frame` now
shares setup-log source preservation with GRAB; the complete GRAB bridge
rebuilds successfully. Nursery cuts landed as `5741911`, all gates passing.
Next: represented initialization, both return suffixes, and generic MAKEBLOCK
composition. Capacity, memory separation and runtime preservation remain explicit.

## Both represented generic MAKEBLOCK initializers

`MakeblockInitializeMore.lean` / `MakeblockInitializeOne.lean`
(`makeblock_initialize_more`, `makeblock_initialize_one`) consume the reservation
and prove the actual header/first-field stores and both native branches. One
adapter generator emits both. The multi-field adapter checks in 1.3 s;
`MakeblockInitialized.copy_start` supplies the actual copy invariant, and
`MakeblockInitInput.copy_after` preserves its source snapshot. Reservation and
log laws landed as `0b3b7c6`, all gates passing. Next: connect the generated
suffixes and assemble the generic MAKEBLOCK arm and successful-step wrapper.

## Complete generic MAKEBLOCK nursery arm

`Makeblock.lean` (`makeblock_arm`, `makeblock_step_arm`) composes dispatch,
reservation, both initializer branches, the actual arbitrary-count copy and
both generated suffixes. `MakeblockFinishMore/One.lean` restores the represented
block through shared `makeblock_restore`; each suffix checks in about 1 s,
and the complete arm plus step wrapper in 0.83 s. This raises coverage to
125 conditional represented opcode bridges. Positive size at most 256,
nonnegative bounded tag, capacity, geometry, placement, source separation and
runtime preservation remain explicit. Larger major-heap allocation remains
open. Initializers landed as `22d5d10`, all gates passing. Next: CLOSURE and
CLOSUREREC, then remaining control, mutation and signed division families.

## Ordinary CLOSURE foundations

Generated zero/nonzero capture prefixes, nursery reservation, zero/nonzero
initializers, both seven-instruction copy branches and the metadata/return
suffix now check. Native costs are 1.4 s for the nonzero prefix, 1.8 s for
reservation, 1.8/2.4 s for initializers, 1.4 s per copy branch and 2.1 s for
the suffix. `ClosureLayout.lean` (`closure_log_layout`) now handles arbitrary
captures; `partial_closure_layout` specializes it with GRAB's environment as
the first capture. `value_log_cons` moved into shared `ReverseCopyLog.lean`.
Both complete GRAB and MAKEBLOCK bridges rebuild successfully. Generic
MAKEBLOCK landed as `1473dcf`, all gates passing. Next: share the indexed-copy
state with RESTART, then connect CLOSURE's represented nursery stages.

## Actual CLOSURE capture loop and shared indexed copy

`IndexedCopyState.lean` parametrizes the indexed endpoint, metadata offset,
registers and native addresses. RESTART indexes its source; CLOSURE indexes
its destination. `ClosureCopy.lean` (`closure_copy_run`) consumes both actual
generated branches (adapters check in 0.96/0.99 s) and proves the entire copy.
`OCaml.Run.counted_loop_native` shares native branch selection with the cursor
loops. `gen_forward_copy.py` now emits all four loop adapters. Complete
RESTART, allocating GRAB and generic MAKEBLOCK rebuild successfully against
the shared abstractions. CLOSURE cuts/layout landed as `a1aa6fb`, all gates
passing. Next: represented CLOSURE nursery stages and allocation restoration.

## Represented ordinary closure restoration

`ClosureRestore.lean` (`closure_allocation_roots`, `closure_restore`) now
assembles captured-value layout, fresh allocation, stack consumption and the
platform invariant from the exact native log. The restoration checks in 0.93 s.
`NurseryInput.lean` shares scalar reservation observations by allocated field
count; GRAB is its specialization. `NurseryInput.frame` transports these facts
through a disjoint prefix, for CLOSURE's accumulator push. Existing GRAB and
MAKEBLOCK bridges rebuild successfully. The shared indexed loop landed as
`47d6c46`, all gates passing. Next: represented CLOSURE prefix, reservation,
initialization and suffix, using the already proved capture loop/restoration.

## Both represented CLOSURE prefixes

`ClosurePrefixMore.lean` / `ClosurePrefixZero.lean` (`closure_prefix_more`,
`closure_prefix_zero`) prove operand decoding and the conditional accumulator
push against the actual native prefixes. The nonempty adapter checks in 0.99 s.
`ClosureFields.frame` shares the persistent count, source, size and code-offset
register observations across the following stages. `addiw_nat_add` now shares
bounded signed-word addition with the copy counter arithmetic. Existing copy
and complete RESTART/GRAB/MAKEBLOCK consumers rebuild. Closure restoration and
nursery transport landed as `3649e9a`, all gates passing. Next: represented
CLOSURE nursery reservation, initialization and metadata/return suffix.

## Represented CLOSURE nursery reservation

`ClosureReserve.lean` (`closure_reserve`) checks in 0.99 s. It transports the
scalar nursery observations through the actual capture push, consumes the
generated reserve span, and preserves shared closure metadata while recording
the exact young-pointer update. `NurseryArithmetic.lean`
(`nursery_sub_reservation`) shares payload-plus-header subtraction.
`ClosureNurseryInput.after` supplies the transported memory observations.
Both represented prefixes landed as `bf98689`, all gates passing. Next:
closure initializer/source snapshot and metadata/return suffix composition.

## Both represented CLOSURE initializers and capture snapshot

`ClosureSnapshot.lean` (`closure_push_snapshot`, `closure_setup_snapshot`)
proves the concrete captured-word snapshot from the push and disjoint nursery
setup. `ClosureInitializeMore/Zero.lean` (`closure_initialize_more`,
`closure_initialize_zero`) then checks both generated header/initializer paths;
the nonempty adapter checks in 1.1 s. `ClosureInitialized.copy_start` and
`ClosureInitInput.copy_after` establish the already-proved indexed capture loop.
The prefix generator now reuses `return_more_guard` for the same signed
nonempty test. Reservation landed as `51e7207`, all gates passing. Next:
shared suffix input for zero/copied captures, metadata stores, and CLOSURE
arm/step composition.

## Complete represented CLOSURE nursery path

`Closure.lean:14` (`closure_arm`, `closure_step_arm`) composes both capture
prefixes, nursery reservation, both initializers, the arbitrary-count generated
copy loop, and metadata/return suffix. `ClosureFinish.lean:15`
(`closure_finish`) reads the preserved displacement, writes code and arity, and
restores `Running`. It checks in 1.1 s; the full composition checks in 0.83 s.
`OperandAt.read32_log` shares operand readback through disjoint write logs.
`ClosureInitialized.ready_zero/ready_copy` shares the suffix input.
The nursery path requires nonnegative capture count at most 254, capacity,
placement, separation, concrete accesses and runtime preservation. The major
allocation and GC paths remain open. Both initializers landed as `12d482e`.

## Generated CLOSUREREC nursery and infix cuts

`Closurerec*Segment.lean` now supplies thirteen generated spans: both capture
prefixes, nursery reservation, both initializers, both capture-copy branches,
one/multiple-function metadata setup, both infix-loop branches, stack
adjustment and return. Corresponding `*_loaded` lemmas project pins from the
executable image; domain-address certificates use `Layout.sym_Caml_state`.
Native spans check in 1.6–6.4 s (copy branches 1.7–1.8 s). The represented
CLOSUREREC composition remains open. CLOSURE landed as `8cbad41`, all gates
passing. Next: share the pointer-copy register shape and prove the actual
CLOSUREREC capture loop, then its metadata/infix construction.

## Shared pointer-copy shape and CLOSUREREC capture loop

`CursorCopyState.lean` now parameterizes the pointer invariant by
`PointerCopyShape`: either source or destination counts the copied words,
with explicit register choices. `PointerCopyAt.index/read/advance` and
`cursor_copy_run_of_branches` share exact logs, image framing and the native
counted-loop fold. Existing GRAB and MAKEBLOCK are specializations.
`ClosurerecCopy.lean:10` (`closurerec_copy_run`) composes the actual six-instruction
branches for arbitrary bounded capture lists. The source address is recovered
from the destination displacement; `difference_copy_address` proves that
normalization. Branch adapters check in 0.95–0.96 s, the fold in 0.78 s.
All complete GRAB/MAKEBLOCK/CLOSURE/RESTART consumers rebuild. Concrete source
snapshot, geometry, separation and fixed destination-base register remain
explicit. Native CLOSUREREC cuts landed as `0e24928`, all gates passing.
Next: recursive-closure prefix/reservation and infix metadata construction.

## Both represented CLOSUREREC prefixes

`ClosurerecPrefixMore/Zero.lean` (`closurerec_prefix_more/zero`) proves both
actual capture-prefix paths through the nursery-size branch. The function
count is positive, capture count nonnegative, and `closurerecSize ≤256`.
`ClosurerecFields` names the persistent metadata separately from allocation
temporaries. `frame_pins` shares register-bundle transport with ordinary
`ClosureFields.frame`. `signed_low32_nat`, `addw_nat_add` and `addiw_nat_pred`
share signed-word arithmetic with the existing count helpers; `closurerec_twice`
handles the metadata stride. Both prefixes check (nonempty: 1.2 s), and existing
complete allocation/copy consumers rebuild. The recursive capture loop landed
as `79c8a1c`, all gates passing. Next: transported recursive nursery reservation,
initializer and metadata/infix loop.

## Represented CLOSUREREC nursery reservation

`ClosurerecReserve.lean:14` (`closurerec_reserve`) proves the actual eleven-
instruction reservation, preserving recursive metadata and allocation size
while recording the exact young-pointer store. It checks in 1.0 s.
`NurseryFrameInput.transport` shares scalar-input preservation through a
pending prefix log; ordinary CLOSURE specializes the same contract.
`gen_closure_reserve.py` now generates both represented reservation adapters.
`nursery_add_reservation` reduces the recursive additive-delta arithmetic to
the existing payload-plus-header subtraction law. Both prefixes landed as
`5e25a86`, all gates passing after a push-race retry. Next: recursive closure
initializer, then infix metadata construction and represented restoration.

## Both represented CLOSUREREC initializers

`ClosurerecInitializeMore/Zero.lean` (`closurerec_initialize_more/zero`)
proves both actual header/initializer paths (1.1 s / 1.0 s).
`ClosurerecInitialized.copy_start` establishes the pointer-copy registers;
`ClosurerecInitInput.copy_after` proves the concrete capture snapshot through
the actual push, reservation and header log, reusing `closure_setup_snapshot`.
`gen_closure_init.py` now generates both ordinary and recursive initializers.
Capture geometry, memory separation and the bounded destination window remain
explicit. The reservation landed as `da971af`, all gates passing. Next: common
zero/copied-capture handoff, first function metadata and the infix loop, then
represented allocation restoration and full CLOSUREREC composition.

## Recursive capture composition and first-function metadata

`ClosurerecSetup.lean:21` (`closurerec_setup`) composes actual dispatch,
prefix, reservation, initialization and arbitrary capture copying through
`ClosurerecReady`; zero captures share the same metadata cut (0.82 s).
`ClosurerecFirstOne/More.lean` (`closurerec_first_one/more`) proves the actual
first stack pointer, code and arity stores. One function reaches the common
return suffix; multiple functions establish named infix-loop registers.
The generated adapters use exact intermediate write logs and the shared
`OperandAt.read32_mem_log` to read the displacement after the stack write.
`gen_closurerec_first.py` generates both paths. Initializers landed as
`d7e21b2`, all gates passing. Next: arbitrary-count infix metadata loop,
stack adjustment/return, simultaneous heap allocation and stack restoration,
and complete CLOSUREREC arm/step composition.

## Actual arbitrary-count CLOSUREREC infix loop

`ClosurerecInfix.lean:10` (`infix_run`) proves the generated continuing and
final infix iterations for every bounded number of remaining functions.
Each fifteen-instruction iteration writes header, stack pointer, arity, then
code pointer. `InfixAt.read_after` proves offset readback after the first two
stores. `GroupedLog.lean` shares finite-block prefix, partial-iteration
separation and exact memory/image advancement. `InfixAt.index/advance` use the
shared native counted-loop fold; arity subtraction also models the unused
final -1 word. Branch adapters check in 4.1–4.2 s; composition in 0.79 s.
`gen_closurerec_infix.py` generates both adapters and the fold.
Finite geometry, offset snapshots/targets, separation and stack room remain
explicit. Setup and first metadata paths landed as `2a0ac08`, all gates passing
after a push-race retry. Next: first-metadata-to-loop bridge, final stack
adjustment and return, then object readback and simultaneous allocation/stack
restoration for the complete CLOSUREREC arm.

## Complete native CLOSUREREC nursery path

`ClosurerecMachine.lean:23` (`closurerec_machine`) composes actual dispatch,
allocation/capture setup, first metadata, arbitrary-count infix construction,
stack adjustment and return (0.84 s). `ClosurerecFirst.infix_start` supplies
loop entry, `InfixRegion.frame` transports offset snapshots through the setup,
and `closurerec_stack/return` establishes the final native stack and bytecode
registers. `ClosurerecReturned` records the exact complete write log and
register frame at the loop head. `Plus.append_steps` shares positive-run
composition through the existing run laws. The infix loop landed as `227712e`,
all gates passing. This is a complete conditional native path, not yet a
represented CLOSUREREC arm: object/stack readback and simultaneous allocation
restoration remain. Next: those memory proofs and the semantic step wrapper.

## Allocation while replacing consumed stack slots

`heap_allocate` in `Primitives/Allocation.lean` factors heap extension out
of `VmPayload.allocate`; the existing payload and reachability APIs remain
wrappers. `payload_rebuild_accu` generalizes fixed-observation restoration
to an updated accumulator. `payload_allocate_stack` in `AllocateStack.lean`
combines old-object framing, fresh-object layout, root restriction and final
stack readback. It allows consumed stack slots to be overwritten, which the
CLOSUREREC log requires. The new stack may contain interior pointers into the
fresh object. The shared target checks in 0.806 s; headline audits added.

## Recursive-closure infix readbacks and roots

`infix_groups_heap_read` and `infix_groups_stack_read` in
`ClosurerecInfixRead.lean` prove every infix header/code/arity word and every
pushed interior pointer after the full grouped log, for arbitrary function
counts. Their geometry is explicit: descending-stack room and the metadata
region below the lowest stack slot. `infix_stores_in` gives each iteration's
two write windows. All groups share `grouped_log_read` and
`grouped_suffix_outside` in `GroupedRead.lean`; earlier writes are arbitrary.
The readback target checks in 1.1 s.

`ClosurerecObject.lean` defines metadata in the exact `BcSem` order and proves
`closurerec_metadata_no_roots`, `closurerec_allocation_roots`, and
`closurerec_stack_roots`. Raw infix headers contribute no locations, captures
are old roots, and pushed interior pointers share the fresh accumulator root.
The object/root target checks in 0.865 s. Headline audits added.

## Complete recursive-closure object layout

`closurerec_log_layout` in `ClosurerecLayout.lean` proves the header and every
field of `closurerecObject` from `closurerecFullLog`: first-function metadata,
all infix triples, and all captures. The hypotheses are represented capture
words, object-size bounds, descending-stack room, and separation of the
complete object from the lowest pushed stack slot. The target checks in 1.0 s.

`ClosurerecMetadataRead.lean` joins arbitrary infix groups using the shared
`value_read_append`/`value_read_cons` adapters to `stack_prepend`.
`ClosurerecMetadataMemory.lean` connects the complete metadata log to those
abstract fields. `ClosurerecEncoding.lean` proves tagged arity and raw infix
header encodings; the group definition preserves `BcSem`'s signed subtraction
from the natural environment offset. `closurerec_function_values_length`
proves the metadata size, and `infix_groups_in` supplies its whole write
footprint. All new headline proofs are audited.

## Complete represented CLOSUREREC nursery arm

`closurerec_arm` and `closurerec_step_arm` in `Closurerec.lean` combine the
actual dispatch/allocation/capture/infix/return execution with complete data
and platform restoration. `closurerec_stack_words` reads every reversed infix
pointer and the first-function pointer above the surviving old tail.
`closurerec_restore` extends the represented heap without requiring consumed
stack slots to survive, frames the runtime and fixed observations, and
restores loop registers. `closurerec_state_of_step` matches the actual `stepI`
CLOSUREREC branch, including signed metadata offsets and all target words.

The full represented arm target checks in 0.828 s; new headlines are audited.
Coverage is now **127 conditional represented opcode bridges overall**, which
includes F2 opcodes; this is not a count out of F1's 134 or a completed
`ArmSim.next`. Nursery capacity, operand/access geometry, heap/stack
separation and runtime preservation remain concrete premises. Major allocation
and GC paths remain open. The complete object layout landed as `b2d8d2a`.

## Signed division native boundaries and unsigned core

`SignedDivisionCuts.lean` imports 15 generated boundaries: all four sign
cases of each libgcc signed wrapper, quotient/remainder return fixups, and
DIVINT/MODINT nonzero caller prefixes/suffixes. The existing arm generator
now handles cross-symbol library cuts; all bytes still come from the pinned
ELF. Segments check in 0.98–1.3 s; image projections check in under 1 s.

`udivdi3_summary` in `Udivdi3.lean` consumes the existing total
`Vsa.Sim.udivdi3_spec` and exposes quotient, remainder, exact memory/output,
complete register frame and initialized scratch registers through named
structures. `BinaryLibInput` shares the operand/scratch interface with
MULINT, whose complete represented arm rebuilds. All new headlines are
audited and generator drift checks cover the new artifacts. The signed
whole-function summaries and represented DIVINT/MODINT arms remain open.
CLOSUREREC landed as `3d99262`; coverage remains 127 conditional bridges.

## Complete signed libgcc summaries

`signed_division_summary` in `SignedDivision.lean` proves both `__divdi3`
and `__moddi3` for all nonzero native divisors, including the most-negative
64-bit operand. Eight generated normalization adapters feed the proved
unsigned core; three generated fixups and the direct quotient return complete
the calls. `division_result_sign` identifies those native results with
`BitVec.sdiv`/`srem`. Exact memory/output and the full clobber frame survive.
The native wrappers return through `t0` where needed and may leave `ra` at
an internal address; the postcondition records the actual clobber set.

`gen_signed_division.py` obtains register pin positions from SegmentEmitter
and generates all eleven adapters; stage a5 checks drift. The complete
summary target checks in 0.773 s, with generated adapters around 0.85–0.9 s.
All headline proofs are audited. The native cuts and unsigned adapter landed
as `1cbbf7a`. DIVINT/MODINT represented caller compositions remain open;
coverage remains 127 conditional bridges.

## Nonzero DIVINT/MODINT represented arms

`Division.lean:division_arm` and `division_step_arm` compose both generated
native callers with `signed_division_summary`, restore `Running`, and agree
with the actual bytecode step. `DivisionArithmetic.lean` proves the 63-bit
unboxing, signed operation and retagging laws, including minimum-value
overflow. Shared `BinaryLibScratch` and `ArithmeticCallFrame` also serve
MULINT. `gen_division_callers.py` generates both caller adapters and is
checked in stage a5.

Target checks passed: arithmetic 0.927s, callers 1.1/1.0s, complete arm
0.831s; MULINT rebuilt after factoring. Coverage is now **129 conditional
represented opcode bridges overall**, including F2 opcodes. This is not a
count out of F1's 134. Zero divisors still require the native exception path.

## Write-barrier caller boundaries

`ModifyCallerCuts.lean` collects fourteen generated native segments and image
projections for SETGLOBAL, SETFIELD0–3, SETFIELD and SETVECTITEM. Prefixes
reach the actual caml_modify entry with its arguments and saved return;
suffixes return to dispatch. The shared segment generator now correctly
constructs an empty PinsHold bundle when replacing its sole register.
All fourteen segments check (prefixes 1.1–1.6s, suffixes 0.95–1.0s).
These are native boundaries, not additional represented arm claims.
Nonzero division arms landed as `0c69b55` with check_all passing.

## Represented write-barrier returns

`ModifyReturn.lean:modify_return_restore` restores Running from separate
named data/platform/register components supplied at the barrier return.
Seven generated `setfield0_return`–`setfield3_return`, `setfield_return`,
`setglobal_return` and `setvectitem_return` adapters execute the actual
suffix and instantiate that restoration (0.92–0.94s each). Their explicit
PC/stack equations account for the different native updates. The shared
callee postcondition requires the changed represented heap, runtime state
and primitive bindings; none is assumed preserved across an actual write.
Caller setup and caml_modify's represented summary remain open. The native
boundary bundle landed as `24a970e` with check_all passing.

## Fixed-index field mutation arms

`ModifyCall.lean:modify_input` frames the full represented VM into the
barrier call using separate named argument/setup/input structures.
`ModifyCallee` names the GC lane's represented caml_modify summary: its
postcondition must supply the edited heap, runtime state, bindings and ABI.
Generated `setfield0_arm`–`setfield3_arm` and matching step wrappers now
compose actual setup, that summary and actual return. Setup reads the
represented stack word, computes the selected field address and advances
the physical stack. The source step wrapper checks setField? and logical
stack consumption. Target times: 0.98–1.1s per complete family instance.
Coverage is **133 conditional represented opcode bridges overall**, including
F2; this is not a count out of F1's 134. `gen_modify_fixed.py` is checked in
a5, with new headlines audited. Represented returns landed as `ffad851`.

## Indexed/global field mutation arms

`setfield_arm`, `setglobal_arm`, `setvectitem_arm` and their step wrappers
now compose native caller setup and return around `ModifyCallee`. Generic
field/global operands use `index_word`; vector indexing uses the total
63-bit `value_index_word`. SETGLOBAL obtains its pointer and read geometry
from Layout.sym_caml_global_data, with the ELF-relative expression checked
against Layout. The generator normalizes native pin observations once for
all three variants. No barrier implementation is assumed read-only: its
represented callee postcondition must establish the heap and runtime.
All three target builds pass; new headlines and generator drift checks are
registered. Coverage is **136 conditional represented opcode bridges
overall**, including F2, not a fraction of F1's 134. Fixed field arms landed
as `15272e3` with check_all passing.

## Shared caught-exception boundaries and loop setup

`RaiseCuts.lean` collects six generated native regions: quiet entries for
RAISE/RERAISE/RAISE_NOTRACE, the caught-handler check, restoration and common
loop-register initialization. All segments check (handler 1.0s, quiet
entries about 1.5s). `LoopSetup.lean:loop_setup` establishes all four fixed
loop registers from pinned instructions, with exact memory/output and
nonwritten-register frames (0.874s). Its constants are checked against
Layout, and both startup and exception proofs can consume it.
These native boundaries do not add represented opcode coverage. Indexed
mutation arms landed as `62aea57` with check_all passing.

## Represented caught-exception frame restoration

`RaiseFrame.lean` names the active, bounded four-word trap frame and proves
its placement at high − 8*trap, exact handler/link/environment/extra reads,
complete stack removal and agreement with the actual raiseTo rule.
`RaiseRestore.lean:raise_restore` restores the represented environment,
extra arguments, surviving stack and updated trap pointer. It reuses the
existing trap-write and return-payload laws, preserving image, bindings and
runtime through the named write footprint. These helpers accept VmPayload
so they apply inside the native handler as well as at loop entry. Frame and
restoration targets check in about 0.95/0.85s. Native handler composition
remains open. Exception boundaries/loop setup landed as `19ae757`.

## Complete native caught-handler restoration

`RaiseHandler.lean:raise_handler` now executes the actual eleven-instruction
handler and shared loop_setup, returning Running for the saved handler
state. It derives the previous trap pointer from the represented tagged
link, proves the trap store leaves the subsequent environment/extra reads
intact, restores the data registers and reinitializes dispatch. Data, frame
geometry, nonnegative saved extra arguments and runtime write preservation
are explicit premises. Target checks in 1.2s; opaque write-log memory avoids
expanding Sail's memory representation. Quiet opcode entries and handler
selection still need composition. Frame/restoration helpers landed as
`2095010` with check_all passing.

## Caught-handler selection

`RaiseState.lean` factors the data/exception context shared by quiet entry,
selection and restoration. `RaiseContext.caught_guard` derives the strict
trap/stack-high comparison from representation and an active trap.
`RaiseCheck.lean:raise_check` executes the six-instruction test, using the
root invocation's equal saved stack-high/external-SP words in
`RaiseStackFrame`, and establishes RaiseHandlerInput (0.912s). The native
branch is proved, not a premise. Nested callback cuts require a relative
boundary. The complete handler rebuilds after the context factoring and
landed previously as `b277e7e` with check_all passing.

## Quiet caught raising arms

Generated `raise_quiet_arm`, `reraise_quiet_arm`, `raise_notrace_quiet_arm`
and matching step wrappers now compose dispatch, quiet native entry,
raise_check, raise_handler and loop_setup. The caught branch is derived
from the represented active trap; quiet domain state, saved root invocation
frame, nonnegative saved extra arguments, RAM/write geometry and runtime
preservation remain named premises. All three complete targets check in
about 0.92–0.97s. `RaiseReadPost` retains memory/native-SP facts between
cuts; `TrapWriteOk.frame` transports write obligations without assuming a
store. Layout's generator now emits off_trap_barrier from domain_state.tbl.
Generator drift checks and headline audits are registered.
Coverage is **139 conditional represented opcode bridges overall**, including
F2, not a fraction of F1's 134. Uncaught, backtrace and debugger paths remain
open. Caught selection landed as `eb3ae96` with check_all passing.

## Native STOP prefix and complete interpreter epilogue

The arm generator now handles both 64-bit and 32-bit stores through the
same width-aware path and code-frame certificates. Existing sd artifacts
remain identical. `tr_stop_prefix` executes callback-depth decrement and
the domain return stores. `InterpReturn.lean:interp_return` executes the
complete shared epilogue, restoring thirteen saved ABI registers, native
SP and return target while returning the accumulator in a0. All save
offsets/frame size come from Layout's prologue extraction; callback-depth
also has its ELF symbol in Layout. `InterpSavedFrame.frame` retains saved
words across disjoint earlier stores. Native segment checks: STOP 3.7s,
epilogue 5.0s; complete epilogue adapter 1.4s. Generator and axiom audits
are registered. This is not yet a STOP machine-halting theorem. Quiet
caught raising arms landed as `e50b59e` with check_all passing.

## STOP return composition

`stop_return` in `OCaml/Vm/Sim/StopReturn.lean` composes the generated
10-instruction STOP prefix with the complete native epilogue. `stopLog`
records callback-depth decrement, extern_sp publication, and external_raise
restoration. Its image and saved-frame separation premises preserve code
pins and all thirteen saved ABI values across the stores. The result
restores caller PC, stack and accumulator result and preserves console
output. The capped build checks the composition in 1.6 seconds.

`stop_halts` in `StopExit.lean` composes this run through the run kernel
with named `StopExitContinuation`. The enclosing startup caller and process
exit must supply that continuation; no unconditional machine halt is
claimed. The original prefix/epilogue landing passed check_all and landed
as `1d1b134` after two push races. Represented opcode count stays 139.

## Represented STOP arm

`StopInvocation.frame_read` factors the saved invocation and store geometry
away from the native STOP entry PC. `stop_arm` composes represented dispatch
with the complete STOP return. `stop_halt_arm` consumes the explicit
`StopExitContinuation`; `stop_halt_step_arm` matches the actual semantic
halt, including its world and exit code. All check under the default limits;
the semantic wrapper module takes 1.7 seconds. Headlines are audited.

Coverage is **140 conditional represented opcode bridges overall**, including
F2 opcodes. This is not unconditional F1 coverage: STOP still requires the
saved native invocation and enclosing process-exit summary. The composed
native return landed as `8024567`, with check_all passing.

## STOP enclosing callers

`caml_main_return` executes the normal-result check and six saved-register
loads, restoring caml_main's caller stack and PC. `main_exit` then executes
the two native instructions calling caml_do_exit with zero. `stop_callers`
composes those boundaries after the proved STOP return, preserving the exact
three-store log and output. `stop_exit_continuation_of_do_exit` reduces the
old caller continuation to the named `StopDoExitSummary` at this actual exit
call site. Debugger/signal cleanup and libc/HTIF exit remain unproved here.

`NativeSavedFrame.frame` now supplies the common saved-word transport for
both interpreter and caml_main frames. The existing interpreter theorem
remains as a specialization. Layout derives caml_main's frame size and slots
from the ELF and checks each restored slot against a native save. The return
adapter generator serves both epilogues; the original interpreter artifact
is unchanged. Capped builds: caml_main segment 1.9s, adapter 1.1s, main call
adapter 0.825s, caller composition 0.818s. The represented STOP arm landed as
`3b41dab`, full gate passing; coverage remains 140 conditional bridges.

## Root uncaught return and startup-compatible quiet barriers

`raise_uncaught_check` proves the root invocation's no-trap comparison and
jump to the uncaught path. `raise_uncaught_return` executes its three stores,
adds the exception-result marker, and consumes the complete interpreter
epilogue. `raise_uncaught` composes both. `UncaughtChecked` records the
read-only boundary; `InterpRuntimeReturnPost` factors the ABI result across
STOP and uncaught returns with their exact, distinct store logs. The
uncaught log reuses STOP's range-separation facts through `uncaught_outside`.
Capped builds: check 1.7s, native return adapter 0.964s, composition 1.3s.

`RaiseQuietReady.barrier` now requires the barrier to be at or above
stack_high. The old equality excluded startup's actual stack_high + one
word (runtime/stacks.c:39). `RaiseQuietReady.below` proves the generated
comparison for every active represented trap; all three caught quiet
adapters rebuild in 1.7–1.8s. This changes an auxiliary arm premise, not the
headline refinement theorem or abstract semantics.

The uncaught bytecode rule enters a pending-exception continuation; connecting
that abstract continuation to native caml_main exception handling remains
open. No additional represented opcode is counted (140 conditional bridges).
The normal caller return landed as `f523550` with check_all passing.

## Terminal C_CALL outcomes

`PrimitiveExitSummary` names the a1-prims obligation for a primitive's
actual `.exit` outcome at its represented call site. `CcallExitCallee` and
`CcallnExitCallee` instantiate the fixed-register and stack-array ABIs.
`dispatch_halts` factors terminal composition through the run kernel.
Generated `c_call{1,2,3,4,5,n}_exit_arm` and `_exit_step_arm` theorems reuse
the checked argument-setup segments and consume those named summaries,
matching both exit status and output world to the actual bytecode rule.
No primitive body or returning suffix is assumed to implement an exit.

All six adapters check at default limits (unary 0.804s; other instances about
0.83s). `gen_ccall_exits.py --check` is registered in a5; all headlines are
audited. No new opcode count is added: coverage remains 140 conditional
bridges, now with terminal outcomes for all C_CALL families. Raising callee
outcomes still need the native longjmp/re-entry and handler continuation.
The uncaught-return/barrier change landed as `a216751`, full gate passing.

## Nonlocal-jump block support

The longjmp path exposed missing unsigned-immediate comparison in the
reflected block model. `MKind.slti` now takes an optional signedness flag,
defaulting to the existing signed instruction. `compareImmOp` and
`execute_compare_imm_char` share SLTI/SLTIU's execution rule through
`compareValue`; the block execution/frame induction is generalized once.
`decodeM` recognizes SLTIU. Capped core builds pass (BlockMem 5.4s).

`gen_nonlocal.py` uses gen_fn's whole-function CFG/block emitter, pinned code
and ELF decoders. `longjmp_shape`, `longjmp_readonly`, and
`longjmp_seqz_decode` check the 17-instruction function's structure and
unsigned seqz operation; generated rows alone are not a whole-function
execution summary. Layout extracts and cross-checks all fourteen jmp_buf
save/restore slots between setjmp and longjmp. Structural certificates check
in 0.836s. Instruction support landed as `8fb720f`, full gate passing.

`longjmp_summary` (`OCaml/Vm/Sim/Longjmp.lean`) now proves the complete
17-instruction native nonlocal return: all fourteen saved registers,
including the saved stack and return address; zero-to-one result adjustment;
unchanged memory/image and the checked register frame. Its input names RAM
reads, saved words, entry registers and aligned continuation. The generated
register evaluator separates pure calculation from memory representation;
individual scalar certificates keep the default elaboration budget. Capped
builds pass: LongjmpFacts 8.3s, final composition 0.986s. This is a native
function summary, not yet the represented C_CALL raising continuation.

C_CALL terminal adapters landed as `6ad2d70`, full gate passing. Coverage
remains 140 conditional opcode bridges.

`longjmp_summary` landed as `543fbb3`, full gate passing.

`reentry_quiet` (`OCaml/Vm/Sim/ReentryQuiet.lean`) proves the native quiet
setjmp continuation through the common handler check: restore the saved
local-roots pointer, load extern_sp and the exception bucket, and follow
the quiet trap/backtrace branches. `reentry_read_outside` checks that this
single store preserves every later domain-field read. Layout extracts the
saved-roots offset and checks its native save; the generated segment uses
pinned instructions. Default-budget builds pass: native segment 2.5s,
state/frame facts 0.866s, complete composition 1.1s. Runtime readiness and
image separation remain named scalar premises. Composition with longjmp
and represented primitive raising outcomes is next.

Quiet re-entry landed as `d873f73`, full gate passing after two push races.

`longjmp_reentry`, `raise_reentry_restore`, `reentry_handler` and
`longjmp_caught` now compose the complete native nonlocal return through
quiet interpreter re-entry and the caught handler, ending in `Running`.
`ReentryMemory` separates reusable scalar readiness from entry registers;
`ReentryControl` shares the final observations with direct/combined native
frames. `CaughtReentryReady` names represented exception memory, native
boundary words, footprint separation and runtime stability. The bridge
uses the existing payload/write-log and handler abstractions. Capped builds
pass at default budgets: longjmp composition 0.850s, represented restoration
0.807s, caught-handler composition 0.835s.

The current F1 primitive table has **no raising or callback outcomes**:
`primF1_outcome` and `primF1_not_raise` (`PrimitiveF1Outcomes.lean`) check
this for every name, argument list, heap and world (11s capped build).
Unsupported outcomes remain outside successful Good executions. F1 C_CALL
therefore needs the existing normal-return/exit adapters; raising primitive
composition belongs to later fragments. The nonlocal bridge is needed now
for DIVINT/MODINT zero-divisor runtime paths. This corrects the earlier
open-work list; no primitive body or semantic rule was changed.

The nonlocal caught-handler bridge and F1 outcome classification landed as
`0538e63`, full gate passing.

`check_global_data_summary` (`CheckGlobalData.lean`) proves the complete
five-instruction normal path when the represented global value is a block
pointer. It preserves memory and all registers except native scratch, and
returns to the aligned caller. `gen_nonlocal.py` now emits whole-function
CFG rows, image projections and a generated audit for check_global_data,
caml_process_pending_actions_with_root_exn, caml_raise and
caml_raise_zero_divide; these last three are generated block certificates,
not yet complete execution summaries. Every helper imports its pinned
per-word ELF decode certificates. Capped builds pass: normal check 3.0s,
and all generated raising-helper rows/image modules. Pending-action fast
return and raising-helper composition remain next.

`check_global_data_summary` and raising-helper certificates landed as
`27b779a`, full gate passing.

`pending_root_summary` (`PendingRoot.lean:8`) proves the complete
nine-instruction no-pending-action return, preserving the argument and native
stack with an exact two-store memory log and executable-image/register frame.
`PendingRootInput` names the 32-bit pending flag, write windows and separation.
Layout extracts and checks pending/raising frame sizes, save slots and the
zero-divide exception-field offset directly from the pinned ELF. Default-budget
capped builds pass: state 0.791s, facts 3.7s, summary 1.8s. Direct-call seams
and caml_raise composition remain open.

The pending-action fast-return summary landed as `a3c168a`, full gate passing
after two push races.

`raise_runtime_prefix` (`RaiseRuntimePrefix.lean:60`) proves the five-instruction
disabled-hook path to the pending call; `raise_runtime_suffix`
(`RaiseRuntimeSuffix.lean:68`) proves the ten-instruction ordinary-exception path
that publishes the exception bucket and prepares longjmp. Both reuse
`registers_of_blocks` for exact effects, image and register frames. Capped builds
pass at default limits (7.8s prefix, 16s suffix). The shared `emit_call` now emits
pinned JAL certificates for all four raising/check helpers; the generated audit
passes with only the permitted axioms. Complete caml_raise and zero-divisor
composition remain next; these boundary summaries do not claim the calls run.

The native raising boundaries and call certificates landed as `9f159b9`,
full gate passing.

`raise_native` (`RaiseNative.lean:41`) proves complete quiet caml_raise execution
through the pending-action fast return and longjmp to the saved native
continuation. `raise_pending` and `raise_longjmp` execute the two pinned JAL
instructions using the shared call bridge. The result carries the exact
four-store log, restored native registers and combined register/output frame.
`RaiseNativeInput` names scalar conditions and separation; VM data restoration
and zero-divisor caller linkage remain open. `EffectPost.nativeFrame` converts
library effects once for native frame composition. Capped default-budget builds
pass: pending composition 1.5s, longjmp composition 0.907s, full raise 0.865s.

Complete quiet caml_raise landed as `264b91d`, full gate passing after one
push race.

`raise_zero` (`RaiseZero.lean:22`) proves complete quiet caml_raise_zero_divide
execution through its global-data check and caml_raise callees to the saved
native continuation. `raise_zero_setup` composes its generated four-instruction
prologue, actual check call/return and three-instruction predefined-exception
load. The combined result carries an exact five-store log and native frame.
`RaiseNativeMemory` separates reusable memory readiness from ABI entry facts;
its `.frame` and `.input` lemmas transport caller stores and establish the actual
callee input. Existing raising summaries rebuild unchanged in meaning. Default
capped builds pass: zero prologue 0.863s, value load 6.9s, readiness transport
0.815s, setup 0.876s, complete zero helper 1.6s. Interpreter DIVINT/MODINT zero
branches and represented restoration remain open.

Complete caml_raise_zero_divide and memory readiness landed as `cf1e5eb`,
full gate passing after two push races and upstream Layout regeneration.

`divint_zero` and `modint_zero` (`DivintZero.lean:12`, `ModintZero.lean:12`)
prove the actual three/four-instruction zero selections. `division_zero_setup`
(`DivisionZeroSetup.lean:18`) proves the shared eight-instruction temporary
frame setup and actual JAL into caml_raise_zero_divide. Its exact log saves
continuation/environment and publishes extern_sp; data addresses come from
Layout. Both branches and setup use gen_arm_pilot; paired branch adapters share
`gen_division_zero.py`, registered in stage a5. Default capped builds pass:
branches 0.813s/0.807s, setup segment 1.5s, complete setup 0.942s. Native helper
composition and represented caught-handler restoration remain open.

The zero selections and shared interpreter setup landed as `efc9210`, full
gate passing after one push race.

`division_zero` (`DivisionZero.lean:41`) proves both complete native zero paths
from their dispatched opcode entries to the saved native continuation. It
composes the generated selector, shared temporary-frame setup, check_global_data,
pending-action return and longjmp via `division_zero_native`. The result has
the exact eight-store log and native register/output frame. `RaiseZeroMemory`
separates ABI entry facts and transports the interpreter stores through all
helper memory conditions. Default capped builds pass: zero-memory transport
0.825s, native shared path 0.881s, complete selector composition 0.854s. These
are scalar native summaries; represented handler restoration and ArmSim linkage
remain open.

Both complete native zero paths landed as `8433537`, full gate passing after
one push race.

`division_zero_caught_step` (`DivisionZeroCaught.lean:11`) composes the complete
dispatched zero path, actual quiet interpreter re-entry and represented handler
with the unchanged bytecode zero-divisor rule. `native_reentry` and
`native_caught` share this composition for arbitrary checked native raising
summaries. Readiness is a data predicate on `nativeMemoryView`, the explicit
write-log memory/output view; no execution is assumed by that predicate.
`division_raise_payload` derives the post-divisor/global-exception payload using
existing root and stack-drop lemmas; `native_memory_last_word` proves exception
publication from the final store. `division_zero_state` identifies the actual
caught bytecode next state. Default capped builds pass (0.78–0.86s per new
module). The full footprint/geometry/runtime readiness supplier and loop-head
dispatch adapter remain open; this does not discharge ArmSim.next.

The represented native re-entry/zero-step composition landed as `07be0bd`,
full gate passing after one push race.

`caught_log_restore` (`CaughtLogRestore.lean:28`) derives the complete caught
readiness on the explicit memory view from pre-raise payload/bindings, footprint
separation, saved geometry and exact-log runtime stability. Handler geometry
is now a separate named part of CaughtReentryReady; all existing compositions
rebuild. `division_raise_payload_before` supplies the divisor-drop/global-root
edit before memory framing. `division_zero_bucket_log` and
`division_zero_exception_word` (`DivisionZeroLog.lean:21,33`) identify and read
back the final exception store; its natural address follows from the valid RAM
window, which rules out wraparound. Default capped builds pass: geometry 0.836s,
restore 0.842s, log/readback 0.800s. Full loop-head footprint/runtime suppliers
and dispatch adaptation are still open.

## Open / next

Immediate next: bridge loop-head dispatch to the native zero inputs and use
`caught_log_restore` in the represented zero arm. The native path, explicit-log
readiness supplier, re-entry/handler composition, payload root/stack edit and
caught bytecode rule are checked. Common invariant suppliers remain open. Consume the remaining caml_do_exit/primitive terminal
summaries when supplied. Continue uncaught semantic continuation/backtrace
paths and major-allocation constructor paths. Later-fragment C_CALL raising
outcomes can reuse the checked nonlocal bridge.
Read landed a1-prims/a6-gc summaries before adding machine work. The approved
`GcSafe P` premise is already threaded through ArmSim and the headline.

The nursery CLOSURE and CLOSUREREC paths, generic/fixed MAKEBLOCK nursery
paths, RESTART, GRAB and APPTERM represented adapters have checked. All six
C_CALL opcodes have setup/return bridges for `.ok` outcomes and consume named
callee summaries. Negative-ATOM and pointer-branch domain gaps remain
recorded above.

The full captured boot `Loaded` witness landed as `bc63ae6`; reset execution
is advancing in a0-boot. Entry and halt remain open. Arm adapters still need
to derive dispatch clock/geometry, operand/heap access, capacity and runtime
preservation from a common invariant preserved by all families. Concrete
GC-boundary and whileMin safety proofs remain to be supplied. No machine
`whileMin` theorem is claimed; `whileMin_bcSem` is bytecode-level.

After the F1 exit, re-read the external brief's After F1 section and continue
F2–F5 in order as a2-sem supplies their semantics. Primitives remain a1-prims'
responsibility; relocation and collector execution remain a6-gc's.
