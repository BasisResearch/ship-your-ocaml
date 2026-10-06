# A1 F1 primitive summaries

## Current status

**Console output (in progress, shared by all channel primitives):**
* `ConsoleWrite.write_console` (`Console/Write.lean`): newlib `_write(fd, buf, n)` on a
  console descriptor prints the buffer by one HTIF putchar per byte (`putchar_step`,
  ported `stepObs_tohost_putchar`; `console_loop` by `loopFromBody`) and returns `n`;
  output = old ++ `bytesToString bytes`; premises `WriteLayout` (96-byte frame) and
  `ConsoleFd` (fs_ready, fd < 32, descriptor kind > 1 and ≠ 4). Generated blocks:
  `gen_fn.py --ocaml-write`.
* `ConsoleWrite.write_fd` (`Console/WriteFd.lean`): `caml_write_fd(fd, flags, buf, n)` on
  a console descriptor returns `n` with the bytes appended to the output and s0–s7
  restored; it writes only `[sp-192, sp)`, `errno` and the reentrancy errno word.
  Premises: `WriteFdLayout`, `ConsoleFd`, the default enter/leave hooks
  (`0x8000d2a4`/`0x8000d2a8`), `_impure_ptr = rp`, `NoPendingSignals`, `n < 2^31`.
  Parts: `enter_blocking`, `write_call` (write → `_write_r` → `write_console`),
  `leave_blocking` (`scan_loop` over the 32 pending-signal slots by `loopFromBody`);
  `indirect_registers_summary` (`IndirectCall.lean`) for the hook's `jalr`.
* `ConsoleWrite.flush_partial` (`Console/Flush.lean`): a console channel's whole buffer
  through one `caml_write_fd` (`flush_written`), or nothing for an empty buffer
  (`flush_empty`); `offset += n`, `curr := buff`, result 1. Shared prologue `flush_head`
  and epilogue `flush_epi`. Memory premises `FlushMem`, transferable over `FlushReads`.
* `ConsoleWrite.ml_flush` (`Console/MlFlush.lean`): `caml_ml_flush(vchannel)` with null
  channel-mutex hooks: local root registered and restored, `flush_partial` once, `Val_unit`.
  Post `MlFlushPost`: output ++ bytes, curr/offset, s0–s11 and sp preserved, memory framed
  outside [sp-384, sp), the errno words, the two channel words and `local_roots`.
  Split by phase (`ml_flush_pro/_enter/_written/_flushed`) to stay within the elaboration
  budget; separation facts in `MlFlushLayout.sep`. The prologue (`ml_flush_pro_gen`,
  input `MlFlushEntry`) and epilogue (`ml_flush_tail`) are shared with the closed channel
  (`fd == -1`, `ml_flush_closed`: straight to the epilogue, generated `closed_fast`).
* Generated block wrappers: `scripts/syi/ocaml_block_wrappers.py` emits `<block>_fast`
  from an access spec (windows, logs over loads, `@k` addresses, branch conditions,
  reloaded ra). Loads after the block's own stores use `BlockPins.accessPlan_of_pure`
  (each load misses only the stores before it). Used for the flush path; the earlier
  hand wrappers (FdWrite/Console/ExitPath `Effects.lean`) are to be migrated, after
  which a discipline rule should forbid hand `registers_of_blocks` wrappers.
* Rules (foreman, 2026-10-06): no new `decide +kernel` over the whileMin run (extend
  `St.shapeOk`); no per-program premises in the headline. Primitive premises are
  native-layout/runtime facts at the call site; the flush adapter's "channel fd is an OS
  output stream" premise belongs to the running-platform invariant.
* Debt: the saved-frame readbacks (`back`/`apart` tuples in write_fd, flush_partial,
  ml_flush, output_char) repeat per primitive; factor a frame-log readback lemma (entries
  `(base + k, 8, v)` plus one extra word) before caml_ml_output_bytes.
* Lean notes: `omega` hits max recursion on `s - 112 - 272` with disjunctions (normalize
  with `Nat.sub_sub`), and evaluates `def` constants like `errnoGlobal.toNat` in
  hypotheses (rewrite them to numerals first).
* `ConsoleWrite.oc_room` / `oc_full` (`Console/OutputChar.lean`): `caml_ml_output_char`
  on a buffered console channel with null mutex hooks; room in the buffer (byte at
  `curr`, `curr + 1`) or full (one `flush_partial` of the 65536-byte buffer, then the
  byte at `buff`). Phases `oc_pro` / `oc_tail` / `oc_full_enter` / `oc_full_flushed`.
* Repr: WorldRepr carries the object-ID counter (`WorldRepr.ooId`), ChanAt the buffer end,
  a clear unbuffered flag, and (last conjunct) `cursor ≤ ioBufferSize ∧ buffer.length ≤
  ioBufferSize ∧ a % 8 = 0` (`ChanAt.fields`/`.cursorLe`/`.bufferLe`/`.aligned`); PayloadOutside/PayloadCoreOutside an `ooId` window.
  `VmPayload.frame_chan` (`ChannelFrame.lean`): payload across a footprint that rewrites one
  channel record, which then represents the channel's new state.
* Console statics: `ConsoleRuntime` (`Console/Runtime.lean`): fds 1/2 consoles, default
  blocking hooks, `_impure_ptr`, no pending signals/actions, null channel-mutex hooks; a6-gc
  pins it for F1 (`f1_consoleRuntime`). Console streams: bprime's `GoodF1.consoles`
  (`OCaml.ConsoleChannels`, out channels with fd ≠ -1). BcSem guards (a2-sem, landed):
  `offsetFits` (offset + n < 2^63) and `isOut` on flushChan/putChar/putBlock.
* Console C_CALL adapters. Shared pieces in `Sim/ConsoleCall.lean`: `consoleWindows sp a`
  (native stack, errno words, a channel record's offset/curr words and buffer) and the named
  premise `ConsoleStable L` over a getD frame (`FrameOnD`; a6-gc: `f1_console_stable`, FIXED
  `consoleStable`), `ChannelArg`/`channel_arg`, `console_geometry` (`ConsoleGeometry` from
  `LoopGeometry` + `NativeValid`; layouts in `Console/Geometry.lean`, addresses checked
  against the ELF by `console_symbols`), `LoopRegisters.of_restored`.
  `caml_ml_flush` (`Sim/PrimMlFlush.lean`): `flush_framed` (open console channel) and
  `flush_closed_framed` (fd = -1) give `FramedPrimitivePost`; the payload/binding apartness
  of the footprint are premises. Waiting on a1-arms (`CcallSetupPost.calleeSaved`,
  channel-record apartness at full extent, transport with a weaker `chans` premise) for
  `prim_caml_ml_flush_returns`. `caml_ml_output_char` (`Sim/PrimMlOutputChar.lean`):
  model inversion (`output_char_semantics`, `PutCharCase`) and the stored byte
  (`char_byte`); next its input (OcLayout from the full-extent geometry) and posts.
* whileMin `PrimReturnsAt` summaries (picked up by `scripts/gen_f1_table.py`; regenerate
  WhileMinTable.lean in the same batch): `prim_caml_ml_string_length_returns` and
  `prim_caml_fresh_oo_id_returns` (`f1_counterStable` from a6-gc's `f1_ignoredStatic`) done.
* Split agreed with bprime (2026-10-06, foreman): bprime takes `caml_format_int` (C_CALL2)
  and `caml_ml_open_descriptor_out` (C_CALL1); a1-prims keeps `caml_ml_flush` (C_CALL1),
  `caml_ml_output_char` (C_CALL2) and `caml_ml_output` (C_CALL4), the flush_partial →
  caml_write_fd → _write chain.
* Next: finish the flush adapter (`ccall_framed_summary`), then output_char, then
  `output_bytes` (a2-sem's `memmove_summary`, `Primitives/Memmove.lean`) and `output`.
* Exit path weakened to `ExitOk` (registers read: ra, sp, a0, s0–s10) for STOP;
  `EffectPost.htifIdle` (`HtifFrame.lean`) for a1-arms' `LoopRegisters.htifIdle`.

**Next (remaining 9, all deep; path-specific callees):**
* `caml_register_named_value`: `strlen` (landed `strlen_summary`), `__umoddi3` hash
  (`DivSpec` battery), `strcmp` chain walk; first registration: `caml_stat_alloc`
  (malloc specs) + `memcpy` (landed) + `caml_register_generational_global_root`
  (skiplist insert, needs a summary); repeat name: `caml_modify_generational_global_root`.
* channels: `open_descriptor_in/out` → `caml_open_descriptor_in` (`caml_stat_alloc`,
  `lseek`) + `caml_alloc_custom_mem`; `output_bytes`/`output_char` (buffer `memmove`,
  `caml_flush_partial` when full); `flush` → `caml_flush_partial` → `caml_write_fd` →
  `write` → `_write` (209-instruction HTIF/FS emulator; check a0-boot's startup rows
  for an existing `_write` summary first); `output` tail-jumps to `output_bytes`;
  `out_channels_list` walks `caml_all_opened_channels`.
* `caml_format_int`: `parse_format` + `caml_alloc_sprintf` (newlib vsnprintf; check
  the A0 `LibraryFormat` specs).

**2026-10-05 (Claude session, taking over from Codex). 21/30 summaries proved.**

* `caml_sys_exit`: `ExitPath.caml_sys_exit_halts` (`OCaml/Vm/Primitives/ExitPath/Primitive.lean`):
  from the represented call site plus the named `ExitRuntime` (VsaOk, native stack
  window `ExitLayout`, the four runtime globals zero), the machine `Halts` with
  `primF1Impl`'s status and console. Machine run `exit_halts` (`Machine.lean`) over
  generated blocks (`gen_fn.py --ocaml-exit`, new stage-a5 check) and the HTIF step
  `store_halts` (ported `Vsa/Sim/TermEntry.lean`). New Layout symbols: caml_verb_gc,
  __atexit, __atexit_recursive_mutex, __stdio_exit_handler.
  `ExitPath.do_exit_halts` (`Machine.lean`) is the shared `caml_do_exit(code)` run from
  its own entry (`DoExitInput`: status in a0, any aligned ra, 208-byte stack window,
  the four globals), with `exitStatus_zero` for STOP: a1-arms/bprime can discharge
  `StopDoExitSummary` from it; `caml_sys_exit_halts` serves the C_CALL
  `PrimitiveExitSummary`.

Done this session:
* `caml_sys_get_argv`: machine run `ArgvTuple.argv_finish_stage`
  (`ArgvTupleFinished.lean`) over the copy/allocation stages (landed `88ba657`);
  `finish_access` discharges the generated finishing block's 13 scalar accesses
  from `FinishLayout` windows, and every loaded value (string root, pair,
  `main_argv`, `Caml_state`, saved ra/s0/s1/s2) is read back from the exact
  write logs (`saved_readback`, `Gc.word_writeLog_at`). Represented contract
  `get_argv_contract` (`GetArgvContract.lean`): payload/bindings framed over
  `getArgvLog`, then two `VmPayload.allocate` steps (name bytes, then the pair
  `[name, World.argv]`). Headline `caml_sys_get_argv_primitive` is generated.
* `caml_sys_get_config`: block certificates from the shared generator backend
  (`ocaml_argv_tuple.emit_tuple_blocks`, argv output byte-identical); stages
  `ConfigTuple{Fast,Copied,Allocated,Finished}.lean`, contract
  `get_config_contract` (`"Unix"` bytes, then `[ostype, 64, false]`), generated
  headline `caml_sys_get_config_primitive`.

Duplication note (law 3): argv and config are two instances of "native frame:
copy a C string, allocate a small block, fill fields". The config stages were
adapted from argv's. A third instance must first factor the stage composition
(prefix block + JAL + callee summary; predicted-memory `finishLoads` with
`lpins8_of_view`; saved-register readback) rather than copy it.

Open, next: `caml_sys_exit` (tail into `caml_do_exit`: halt behaviour), the
channel family (`open_descriptor_in/out` via malloc and custom alloc,
`out_channels_list`, `flush`, `output_char`, `output`=tail jump to
`output_bytes`), `caml_format_int` (`parse_format` + `caml_alloc_sprintf`),
`caml_register_named_value`.

Executable-name allocation now passes its focused build: 18/30 summaries
proved, with full copy-string/memcpy execution and represented fresh bytes.
The complete 2,023-target build and axiom audit pass (standard axioms only);
landed at `9ba7eef` after the complete integration gate. Twelve remain.

Started `lane/a1-prims` from origin/main (`bf5d5df`) in the reused a0-lib
worktree. Read the lane brief, COMMON.md, CLAUDE.md, PLAN.md and PHASES.md;
ran the abstraction inventory. The landed `PlatformOk`/`Running` contract is
in scope. Nine constant primitive summaries are proved and landed at `c4b42e0`;
the first milestone passed the complete integration gate. Signed integer
comparison is now proved (10/30 total), with its shared read-only register
frame and tagged-order lemmas. The complete axiom audit passes (1,083 targets,
standard axioms only) and the milestone is landed at `d4ebfc4`.
Argv and both string/bytes length summaries now build against the migrated ELF
(13/30 proved). Their shared heap/access-window bridge and code certificates
compile within the default budgets. The complete build and axiom audit pass
(1,119 targets; only the permitted standard axioms). The complete integration
gate passed and the accessor milestone is landed at `029d516`.

`caml_fresh_oo_id` is proved (14/30 total), including the updated counter
and VM payload frame. Its generated module compiles in 1.7 seconds; the complete
regression build and axiom audit pass (1,273 targets, standard axioms only).
The complete integration gate passed and the milestone landed at `54ce77c`
(39,560 pinned bytes, zero mismatches).

`caml_string_equal_primitive` now compiles (15/30 proved), including alias,
unequal-size and finite word-loop paths. The full build and axiom audit pass
(1,343 targets, permitted standard axioms only). The complete integration
gate passed after rebasing concurrent boot/arm work, and the milestone landed
at `24ef4c7`.

`caml_string_notequal_primitive` is proved (16/30), with a generated native
stack save/JAL/restore wrapper around the equality summary. The complete
machine call splice and represented contract pass their focused build; the
full regression and axiom audit pass (1,891 targets; standard axioms only).
The complete integration gate passed and the milestone landed at `5aec151`. The native sp is restored, and the saved
return-address write is framed from the represented heap/world and primitive
bindings using explicit static separation. The whole wrapper uses the default
proof budgets.

## Inventory and next work

`results/primitives-f1.json`, regenerated by `scripts/gen_primitive_census.py`,
records all 30 `primsF1` entries, instruction counts, and external/indirect
transfers from the pinned ELF. `gen_layout.py` now emits their symbol addresses
and the three primitive globals `main_argv`, `caml_exe_name`, and `oo_last_id`.

Nine system constants share a register-only leaf shape (two instructions,
three for max_wosize). They now use the `gen_fn.py --ocaml-constants` backend,
which calls the original CFG extractor and folds the existing segment kernel.
Integer comparison uses `--ocaml-compare`; argv and length accessors use
`--ocaml-argv`/`--ocaml-lengths`. The six-instruction `--ocaml-counter`
family reads and updates `Layout.sym_oo_last_id` with a shared memory-region
frame and explicit link to `World.ooId`. Next are the allocating/channel primitives and process exit. Calls and tail calls
will use `FnSummary.callSplice` / `tailJump` and the landed A0 library specs.

The unused legacy generator backend still has WHILE-specific path defaults
and only folds a counted byte-output loop. The new ELF backend emits neither
budget overrides nor unavailable import assumptions.

The current `WorldRepr` constrains console/channels but not argv's global,
executable-name storage, the object-ID counter, or named-value table contents.
Those primitive-specific input invariants must be made explicit and preserved.
`VmReprAt.atHead` is a dispatch-loop predicate, so a primitive-call boundary
must separate its data representation from PC and argument/result registers.
The arbitrary `Layout.runtimeOk` also needs an explicit frame-stability
interface before preservation can follow from a callee's register/memory frame.

The string equality ELF compares complete words, including padding. `ObjAt`
currently records payload bytes and the final padding-count byte, but not
intermediate zero padding. The string family therefore needs an explicit
padding invariant supplied by `caml_alloc_string` (`runtime/alloc.c:93` zeros
the final word before writing its count byte); the current representation
alone does not justify whole-word equality.

## Primitive theorem table

Each theorem is in `OCaml/Vm/Primitives/<module>.lean` and generated by
`gen_fn.py` with `--ocaml-constants`, `--ocaml-compare`, `--ocaml-argv`,
`--ocaml-lengths`, `--ocaml-counter`, `--ocaml-string-scan`, or `--ocaml-string-wrapper`. The `_primitive` theorem connects the C entry
and return to `primF1Impl`, carries the represented VM payload/result, and
preserves the platform and saved caller registers. Read-only callers supply
`MemoryStable runtimeOk`; `runtime_memory_stable` proves this for the current
`RuntimeOk` from the free-list predicate's memory-frame law. The counter
uses `WindowStable` plus payload/table separation. String equality also
requires the named `PaddedString` allocator invariant.

| Primitive | Theorem | File:line |
|---|---|---|
| `caml_sys_const_naked_pointers_checked` | `caml_sys_const_naked_pointers_checked_primitive` | `CamlSysConstNakedPointersChecked.lean:95` |
| `caml_sys_const_big_endian` | `caml_sys_const_big_endian_primitive` | `CamlSysConstBigEndian.lean:95` |
| `caml_sys_const_word_size` | `caml_sys_const_word_size_primitive` | `CamlSysConstWordSize.lean:95` |
| `caml_sys_const_int_size` | `caml_sys_const_int_size_primitive` | `CamlSysConstIntSize.lean:95` |
| `caml_sys_const_max_wosize` | `caml_sys_const_max_wosize_primitive` | `CamlSysConstMaxWosize.lean:113` |
| `caml_sys_const_ostype_unix` | `caml_sys_const_ostype_unix_primitive` | `CamlSysConstOstypeUnix.lean:95` |
| `caml_sys_const_ostype_win32` | `caml_sys_const_ostype_win32_primitive` | `CamlSysConstOstypeWin32.lean:95` |
| `caml_sys_const_ostype_cygwin` | `caml_sys_const_ostype_cygwin_primitive` | `CamlSysConstOstypeCygwin.lean:95` |
| `caml_sys_const_backend_type` | `caml_sys_const_backend_type_primitive` | `CamlSysConstBackendType.lean:95` |
| `caml_int_compare` | `caml_int_compare_primitive` | `CamlIntCompare.lean:172` |
| `caml_sys_argv` | `caml_sys_argv_primitive` | `CamlSysArgv.lean:122` |
| `caml_ml_string_length` | `caml_ml_string_length_primitive` | `CamlMlStringLength.lean:350` |
| `caml_ml_bytes_length` | `caml_ml_bytes_length_primitive` | `CamlMlBytesLength.lean:350` |
| `caml_fresh_oo_id` | `caml_fresh_oo_id_primitive` | `CamlFreshOoId.lean:204` |
| `caml_string_equal` | `caml_string_equal_primitive` | `CamlStringEqual.lean:7` |
| `caml_string_notequal` | `caml_string_notequal_primitive` | `CamlStringNotequal.lean:7` |
| `caml_int64_float_of_bits` | `caml_int64_float_of_bits_primitive` | `CamlInt64FloatOfBits.lean:7` |



`BlockInput` certificates are fully discharged by generated pins/decodes,
register inputs, return alignment and finite shape checks. They are not
assumed as primitive execution premises. `VmPayload` is the memory/world
part of `VmReprAt` at a C-call boundary: `Setup_for_c_call` temporarily changes
sp and PC; the arm's generated restore segment supplies the loop-head register
view. The callee post includes a0, caller return PC, all other non-noise
registers (except a5 as well for comparison), memory, output, `GoodState`,
image pins, runtime and loop registers.

All nine modules build within the default heartbeat budget (about 2 seconds
each). Explicit finite symbolic evaluation avoids a deep kernel reduction in
the max_wosize shift case. Shared payload/root restriction and runtime frame
lemmas compile. The abstraction gate and discipline checks pass. The full
`OCaml.Audit` build passes (1,060 targets); all nine primitive theorems and
shared adapters use only `propext`, `Classical.choice`, and `Quot.sound`.
The full build passes. The audit gate normalizes wrapped axiom lists before applying its unchanged
allow-list, rejects Lean process errors explicitly, and builds the Audit target
so freshly imported audit dependencies cannot be missing.
The nine-primitive milestone passed the full integration gate and is landed; no semantic
changes were made to `primF1Impl`.

## Signed comparison milestone

`tag_toNat`, `tag_toInt`, and `tag_signed_lt` establish signed order for all
63-bit OCaml integers. The generated six-instruction summary returns the
`primF1Impl` comparison value, preserves VM data and the platform, and frames
all registers outside a0/a5 and the machine noise registers.
`ImmediateInput.arguments` records each represented argument in its C ABI
register. `PreservesLoopRegisters [10, 15]` is a discharged finite check.
`register_of_blocks` now supplies the common frame proof for constants,
comparison, and upcoming read-only accessors; `Leaf` reuses it.

## ELF migration coordination

The foreman announced a pending fixed-address `.embed` image migration.
Function addresses stay fixed while data addresses and relative immediates
change. All data references use `Layout`; after that landing, rebase and run
the primitive generators again to refresh pins and per-word decode imports.

## Read-only accessor work

`caml_sys_argv_primitive` compiles against the migrated ELF, with the explicit
`valWord pl s.world.argv = some (word c Layout.sym_main_argv)` precondition.
`VmPayload.accu_of_root` and `readOnly_contract` preserve the heap placement
when returning an existing root; immediate contracts specialize the same rule.

The generated string/bytes length summaries compile in about 2.5 seconds each
within the default proof budgets. Both length instances share `StringInput`/`string_length_contract`;
`StringGeometry` supplies RAM/HTIF exclusion bounds, with data addresses from
`Layout`. `StringInput.shape` derives header size and the final padding count
from the represented live object. `stringLengthWord_tag` proves the tagged
result for arbitrary represented string lengths.

The generator emits literal instruction records certified by `ElfDecode`,
separate code/static certificates, and a load-prefix register checkpoint.
`Control.memory_free_facts` handles register-only spans without inspecting
data operands. `ReadWindow.ld`/`.lbu` package total-byte observations and access
bounds, preventing large scalar-load simplification proofs. `readonly_wlog`
proves the empty write log from instruction syntax. These helpers add no
machine run law or execution premise.

Rebased on the fixed-embed migration `7fa1750` and regenerated the primitive
census and all four primitive generator families. Generator drift, proof
discipline and the abstraction gate pass. All 39,240 pinned bytes match the
ELF. The complete build and axiom audit pass (1,119 targets; standard axioms only). Builds run only with at least 25 GB
available and under the 24 GB cap.

## Mutable-global work

`caml_fresh_oo_id_primitive` returns the old tagged global and stores its
increment, matching `primF1Impl`. The write-effect post generalizes the
read-only register frame, and its VM frame reuses `writeLog_out`,
`FixedBytesLoaded.transport`, and relocation `Eqv.transport` at identity.
`PayloadOutside` describes static separation of the write log from VM
observations; allocator placement and stack/code/global separation will supply
it. The generated six-instruction certificate uses `ReadWindow.ld` and
`WriteWindow.sd`; `counter_contract` connects the exact write log to the
abstract world update. `WindowStable` records the runtime invariant’s
required frame law over the counter window. No execution premise is assumed.

## Current follow-up

The rebase includes the arms lane’s `PrimitiveBindings` repair. Primitive
input/post records now carry this metadata; read-only summaries use its
existing memory frame, while `BindingsOutside` supplies the two table
observations needed for a disjoint write-log frame. All fourteen summaries
and the full axiom audit pass (1,334 targets, standard axioms only).

`PaddedString` records the allocator’s canonical zero padding. The shared
word-to-byte bridge reuses `bytesT_extract` and `Reloc.Copied` to connect the
ELF’s full-word comparisons to abstract string contents.
`PaddedString.eq_iff_words` proves equivalence in both directions, including
length recovery from the final padding-count byte. Both string summaries consume this explicit allocator invariant.

## String scan progress

The binding/canonical-string milestone landed at `2f8530a` after the full gate.
`gen_fn.py --ocaml-string-scan` now emits nine CFG block certificates for
`caml_string_equal`, including both branch outcomes. Fixed-point register
liveness retains the values needed across loop joins. The complete generated
module compiles in 5.5 seconds at the default budgets.

`BoundaryPost` packages a shared read-only ABI/image/register frame;
`boundary_bind` composes generated summaries through the existing triple rule.
`StringScan.scan_iteration`, `scan_loop`, and `scan_words` compile (the loop
module takes 1.9 seconds). They use `loopFromBody`, a decreasing word count,
an equal-prefix invariant, and a mismatch witness. No run induction was added.
The entry paths and the `primF1Impl` bridge are proved and landed.

The entry composition now compiles in 1.1 seconds. Signed load offsets in
the generator use explicit bit-vector subtraction, so existing header-address
lemmas apply without expanding byte values. `string_comparison_value` connects
the complete machine decision to the byte-list equality in `primF1Impl`;
`caml_string_equal_primitive` is the generated represented-call headline.
Next is the stack-writing `caml_string_notequal` call wrapper.

## Inequality call wrapper

`caml_string_notequal` saves ra in a 16-byte native-stack frame, calls
`caml_string_equal`, restores ra/sp, and subtracts the tagged result from 4.
The complete-register call adapter `Vsa.Sim.bridgeOfSegFull` is ported from
upstream commit `1453d2e` (source read only; see ATTRIBUTION.md).
A common `CallInstr`/`CallShape`/`CallDecode` adapter connects generated
ElfDecode and code-pin facts to that bridge. `wrapper_enter`, `wrapper_equal`,
and `wrapper_leave` compose with `FnSummary.callSplice`; the complete
`string_notequal_machine` compiles in 1.4 seconds. `StringNotEqualInput`
records the native stack window, image/payload/table separation, and argument
object separation. `PaddedString.frame_log` preserves the allocator invariant
using `Reloc.Copied`. The represented contract compiles in 16 seconds.
The generated wrapper certificates compile in 1.9 seconds; finite sign-extension
certificates avoid deep normalization of symbolic addresses. No budgets were
raised. The abstraction gate passes (C1=0, C2=7, C3=7, C4=3), as does discipline.


## Allocating primitive follow-up

The next shared component is heap-allocation transport: the old reachable
objects retain their placement and one fresh result object becomes reachable.
The `caml_int64_float_of_bits` tail call enters `caml_copy_double`; its nursery
fast path writes young_ptr, a double header and one payload word. The slow
path calls `caml_alloc_small_dispatch` and needs collector integration. This
primitive remains open; a fast-path lemma alone will not be counted as the
complete primitive.

`VmPayload.allocate` and `allocation_contract` now build. They reuse the
symbolic heap allocation laws and classify post-allocation reachability as
fresh or old; fresh-object fields must point to old live objects. A placement
can reserve its unreachable fresh key before the call. No relocation or run
induction is introduced.

`gen_fn.py --ocaml-allocation` emits both nursery blocks, code pins, scalar
access certificates, exact write-log equations and `FnSummary` folds.
`DoubleAllocation.copy_double_fast` composes the blocks with `summary_bind`
and proves the complete successful nursery path. `double_layout` connects
the exact log to the double object's header and bit payload (253 tag, one word). The collector
branch and the primitive's input/tail-jump bridge remain open, so the total
stays **16/30**. These are reusable support results, not a seventeenth primitive.

Allocation-support validation: full regression and audit pass (1,918 targets;
permitted standard axioms only). Generator drift, discipline and a8 pass.

Allocation support landed at `0c3d49d` after the complete integration gate.

## Named-value model correction

The C runtime (`runtime/callback.c:203–227`) updates the matching root slot;
the former model appended a duplicate. Since `roots` includes `World.named`,
that retained an obsolete value as a GC root. C names also end at the first
NUL byte, whereas the former model used the complete OCaml byte string.
`scripts/validate_named_values.py` probes both cases against the host 4.14.4
runtime through `caml_named_value`: replacement yields 22, and two names
sharing their pre-NUL prefix yield 44. The model transcription now uses
`namedValueKey` and `registerNamedValue`. All ten host/model difftests pass
(`results/bc-named.json`), including the new `f1_named` registration sequence.
The direct host table probe supplements stdout/exit comparison.
`OCaml/Bytecode/NamedValues.lean` proves latest-key lookup, other-key framing,
retained-root membership, and the actual primitive replacement transition. No machine primitive is counted by this repair.

Named-value correction validation: full regression/audit passes (1,965 targets,
standard axioms only); discipline, generator checks and a8 pass.

The named-value correction landed at `d05db1f` through the full gate.

## G1 allocating primitive contracts

PLAN.md §3 selects G1 (no collection after the cut) for the initial F1–F3
refinement. Accordingly, allocating primitive summaries will carry explicit
allocation-room and metadata-separation premises supplied from the budget and
runtime invariant. Their G1 machine summaries do not require completing the
A6 collector branch. The double constructor support is ready; its int64
payload-load/tail-call and represented allocation bridge are being connected.

`int64_float_machine` now composes the generated boxed-payload load and tail
jump with `copy_double_fast`, using `FnSummary.tailJump`. The complete G1
represented allocation contract compiles: `Int64FloatInput` supplies the
represented source object, RAM bound, reserved fresh placement, separation
and nursery room. `AllocationRuntime` is the chosen runtime predicate's
memory-effect frame supplier; no machine execution is assumed by that
premise. The result heap gains exactly `.double bits` and the world is
unchanged. `BoundaryPost.then_write` factors the read-only-prefix/write-log
composition so concrete memory maps remain opaque during elaboration.
The generated headline and full regression/audit pass (2,103 targets, standard
axioms only), with **17/30 G1 summaries proved**. The milestone landed at `8658c0d` through the complete gate; the
collector-enabled extension remains A6.


## Library call adapter

The next library consumers use the landed `SnpW`/`LocalRun` certificates
(strlen, formatting and allocator wrappers). A shared bridge is being built
with `loopFromBody` and the existing machine run-kernel adapters. Its measure
is the least remaining bounded certificate; it introduces no run induction.
The post must retain total-byte/output observations, the facts these library
specs provide, and must not claim exact optional-memory-map equality.

`localRun_triple` and `symbolic_summary` now compile; `strlen_summary`
instantiates the landed `strlen_nw` certificate, retaining return PC, length,
non-scratch registers and unchanged total bytes (`strlen_memory`). Both
modules compile at the default elaboration budget (about one second each).
These are shared support, so the primitive count remains 17/30. The next
step is observational VM framing and the generated string-allocation caller.

Library bridge landed at `21fe0a3`, including the full gate and axiom audit.
`VmPayload.frame_observedLog` now generalizes the existing write-log frame
using `MemEqv` and observable output; `frame_log` remains its exact-map
specialization. `frame_observed` supplies the read-only case. Object and
channel transport still use the existing relocation combinators.
`LibraryFrame.lean` recovers optional ABI/PC values from `VsaOk`, preserves
primitive bindings, and restores exact code pins from byte observations plus
live-memory presence. `strlen_leaf` and `strlen_result` supply the next
generated caller segment's ABI input and length. Focused builds pass.

Observational frames landed at `19470f8` through the full gate. Nursery work
now shares `AccessPlan` and `scripts/syi/ocaml_nursery.py`: generated
`SmallAllocation` reserve/initialize and `StringAllocation`
prepare/reserve/initialize block summaries compile from this ELF. String
initialization's internal fallthrough split is merged along the selected
nursery path. Concrete string-prefix stack/size facts are in progress;
reservation, padding layout and caller composition remain open. No new
primitive is counted by these block certificates.

The three string block effect theorems now compile: `prepare_fast`,
`reserve_fast`, `initialize_fast`. `prepare_access` and `reserve_access`
discharge scalar accesses from explicit RAM/write windows and total load
pins. Initialization still takes its finite `AccessPlan`; discharge of that
plan, whole-constructor composition and string layout remain next.
The initialization write log required small explicit constant certificates
instead of eager global simplification; no budget increase was used.
Discipline and abstraction checks pass (C1=0, C2=7, C3=7, C4=3).

Nursery block certificates landed at `5984250`. The complete
`alloc_string_nursery` function summary now composes all three blocks and
restores native `sp`, retaining the exact combined write log.
`initialize_access` supplies all six scalar accesses from RAM/write windows
and post-store pins. `nursery_readback` discharges those post-store reads
from `NurseryMetadata` plus stack/header/metadata separation, without an
execution premise. Focused builds pass at the default budget.

Next: string header/padding layout, the copy-string caller, and full memcpy.
The existing local `MemcpySpec` only certifies the byte-loop entry; upstream
`syi-absint-merge` at `1453d2e1` also has `MemcpyLoops.memcpyLocalRun` covering
dispatch/alignment/word/bulk/byte paths. Reuse and retarget that proof for the
caller instead of limiting executable names to the short byte-copy path.
The primitive count remains 17/30 until represented caller contracts land.

The complete nursery constructor/readback support landed at `74e6126`
(after one fast-forward race and a repeated successful gate). Full memcpy
is being ported through the existing allocator-template generator, with
its source interpreter import dependencies cut at pure byte facts. The
source is read-only `syi-absint-merge` commit `1453d2e1`; provenance is in
ATTRIBUTION.md. Constructor string layout and copy-string caller remain
open alongside that port.

Full memcpy now compiles at the default budget (loop module about 21s,
`memcpy_summary` bridge about 1.4s). `image_local` recovers exact immutable
code pins from the confined write frame and live-byte presence. The bridge
returns `LeafInput`, represented copy bytes and the complete observational
frame. The import cut now reuses `MemcpySites2.ldData8`, avoiding a duplicate
definition in `LibraryByteFacts`; its users remain source-generated.
Discipline and a8 pass unchanged. This closes library support, not a new
primitive count. Next is the string layout/copy-string represented caller.


2026-10-02 resume: full memcpy landed at `6d1b6b7`; rebased on current
main and regenerated every F1 family, census and library template. The
fixed-embed ELF migration is included and regeneration introduces no drift.

Library composition now preserves presence through generated writes:
`LibraryEffects.lean:10` (`RegistersPost.vsaOk`) reuses the existing write-log
presence and register frame laws. `StringNursery.NurseryPost` retains this
invariant universally for any caller-supplied live-byte set; no additional
execution assumption was introduced. The previously private
`VsaIris.Inst.gpr_avoids_noise` certificate is public for reuse.

`StringAllocationArithmetic.lean` proves word count, rounded span, header
encoding and padding subtraction at the default budget. `StringAllocationLayout.lean`
proves `shell_layout` from the canonical three-store log, then
`StringShell.object` and `.padded` complete the representation once the
payload bytes are supplied. Splitting the write log explicitly avoids a
unification timeout without changing any proof budget. Focused builds pass.

Still 17/30 primitive summaries. Next: relate the actual initializer log to
`shellLog`, preserve the shell across the confined memcpy write, generate the
copy-string caller boundaries and compose the executable-name primitive.

The actual initializer log is now normalized by `initialization_shell_log`
(`StringConstructorLayout.lean:9`), and `NurseryPost.shell` supplies the layout
directly from the machine constructor's postcondition. `StringShell.frame_payload`
preserves header/padding across a copy confined to the data bytes. The full
1974-target audit rebuild passed; the final layout bridge is included in the
next audit. Next is the generated copy-string call composition.


String layout/invariant support landed as `55667f5`. The copy-string generator
now emits four CFG boundary certificates and all three direct-call pins,
shapes and ElfDecode adapters. `ocaml_block_certificates.emit_block` is shared
with the nursery generator; its existing outputs are byte-for-byte unchanged.
`StringCopyFast.{save,size,arguments,restore}_fast` supply the four boundaries
from stack windows and memory pins, with exact effects and register interfaces.
All focused builds pass without increased budgets. The whole copy-string
composition and represented primitive contract are next; the count is 17/30.


Copy-string boundaries landed at `c0f2125`. The actual composition now covers
entry through `strlen` (`StringCopySized.copy_string_sized`), the length store,
the allocation JAL, and the complete G1 constructor
(`StringCopyAllocated.copy_string_allocated`). It returns the allocated shell
at the memcpy-argument boundary. `caller_readback` proves all three native
save slots from the combined write log and explicit later-store separation.

Shared adapters now expose generated GPR/RO frames and transport total-byte
equality through write logs. `strlen_call` instantiates the landed symbolic
reader at actual caller register observations. `NurseryGeometry` separates
static RAM/guard/image conditions from per-state inputs, and the constructor
post retains the restored `ra`. Focused builds all pass. The next step is
memcpy plus restore, then the executable-name tail and represented allocation
contract. The primitive count remains 17/30 until that contract is landed.


The complete native string copy now composes all three calls and the return:
`StringCopy.copy_string_finish` and `StringCopy.copy_string_machine` preserve
byte observations, the string shell, ABI registers and the native stack.
The generated executable-name tail loads `Layout.sym_caml_exe_name`.
`executable_name_contract` extends the represented heap with its copied bytes,
frames the old payload/bindings and preserves the running platform. Explicit
G1 nursery-room, placement/separation and memory-observation runtime premises
are supplied by callers; none assumes execution or the desired postcondition.
`MemoryFrame` now supports pointwise footprint frames while retaining its old
exact/observational log APIs. Focused builds pass at default proof budgets.

| Primitive | Theorem | Location |
| --- | --- | --- |
| `caml_sys_executable_name` | `caml_sys_executable_name_primitive` | `CamlSysExecutableName.lean:7` |
| `caml_sys_get_argv` | `caml_sys_get_argv_primitive` | `CamlSysGetArgv.lean:7` |
| `caml_sys_get_config` | `caml_sys_get_config_primitive` | `CamlSysGetConfig.lean:7` |

Next: allocating configuration/argv and channel primitives, named-value
registration, output/formatting and process exit. The exit remains 30/30 landed
and audited; this milestone does not close the lane.

Small-block nursery composition is next, shared by configuration/argv tuple
allocation. The generated two-block certificates already exist; register
evaluations and scalar effect adapters are under construction.


`SmallAllocation.alloc_small_nursery` (`SmallNursery.lean:45`) now proves
reservation, header initialization and return for the G1 path. It exposes
an exact two-store log, preserves the return address, and transports the
library presence invariant. `blockHeader_ok` and `NurseryPost.header`
(`SmallLayout.lean:17,26`) connect its initialized header to object layout.
The two generated blocks share scalar access-plan/effect adapters in
`SmallFast.lean`; all focused builds pass at default budgets.

The argv-pair caller now has three generated boundary summaries and two
JAL adapters in `ArgvTuple.lean`. Call-pin emission moved into the shared
`ocaml_block_certificates.emit_call`; existing string-copy artifacts remain
byte-for-byte unchanged. Full caller composition and represented two-object
allocation are still open. No additional primitive is counted (18/30).
Discipline and a8 pass: C1=0, C2=7, C3=7, C4=3.


Small allocation and argv boundaries landed as `2826b17`, after a complete
gate and one push race. The three argv boundary effect wrappers now compile
in `ArgvTupleFast.lean`. Generated store-log certificates use bounded chunks
and `Vsa.Sim.wlogM_append`; unrestricted simplification of the full stack log
caused rapid memory growth, so those exact processes were stopped and the
proof was factored. Raw base-plus-offset addresses and definitional store
certificates keep the checked replacement within the default budgets.

`SizedMemory`, `AllocateMemory`, and `CopyMemory` separate static memory
requirements from dynamic leaf/stack/library entry facts. The existing
`CopyInput` interface remains compatible, and the executable-name contract
rebuilds successfully. Next is full argv call composition and its represented
two-object allocation; the landed primitive count remains 18/30.
