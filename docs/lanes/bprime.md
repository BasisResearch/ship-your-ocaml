# Lane bprime

## Decimal native alloc_sprintf return (2026-10-28): checked for lead review

Resumed checkpoint `5d6bc04f`, preserving its successful proof composition.
Read the binding task, `CLAUDE.md`, relevant `PHASES.md`/`PLAN.md` and
dead-end/lane sections; ran `scripts/abs_inventory.sh` before proof review.
The inherited `/tmp/sprintf-native-build7.log` completed **1,403 jobs**,
including `AllocSprintfEntry` and `AllocSprintfNative`.

`AllocSprintfLong.native_return` in `Format/AllocSprintfNative.lean` proves
`FnSummary 0x80013ec4` through the original native `R 1` return for precisely
the plain signed LONGINT decimal path. Its `NativeInput` has initial
register/data, geometry, runtime and separation requirements; no execution,
primitive return or C_CALL return is a premise.

- `AllocSprintfEntry.enter` reuses generated `pro_fast` and the decoded JAL
  to `vsnprintf` at `0x8004018c`. The eleven prologue stores establish the
  first vararg and original ra/s0/s2 save bank. `VsnLongEntry` and
  `SymbolicInput` follow from those stores and initial library/data facts.
  The local base is `sp`, original stack and parsed `%ld` are at `sp + 240`,
  buffer at `sp + 16`, and seven spill slots at `sp + 184` through `sp + 240`
  (exclusive). `snpAbove = 192` keeps the parsed format outside ownership.
- `to_return` composes `enter`, `vsnprintf_long_summary` and the existing
  `short_initialized` with `summary_bind`/`FnSummary` call composition.
  It reuses `decimal_buffer`, `decimal_fits` and `decimal_nursery_small`:
  signed 64-bit decimal has length ≤20 and fits the 128-byte buffer with
  its NUL. The actual short call at `0x80013f1c` targets initialized-string
  entry `0x8000c284`; that proof executes nursery allocation and memcpy
  and returns to `0x80013f20`.
- `finish_return` reuses generated `done_fast`, loading original ra/s0/s2
  and restoring the original stack, a0 result and all ABI saved registers.
  `NativePost` retains aligned result, exact `decimalBytes (R 11)`
  (`strBytes (intToString (R 11).toInt)`), length, header/padding layout,
  observable output and total-byte memory facts. `NativePost.object`
  exposes `ObjAt ... (.bytes (decimalPayload (R 11)))`.
- `NativePost.live` uses `LiveFrame.of_foot` for the selected arena-owned
  blocks under its explicit bounds/footprint separation premise; `GprsSame`
  composes register frames and `LogInW`/`frameOn_writeLog` frames the
  prologue. Outside the enclosing native stack window, `effects` gives
  the actual initialized-string metadata/save log plus byte-copy log
  relative to the original memory. `preserved` gives unchanged bytes outside
  the stack/allocation/copy footprint. `WriteLogObservation` transports
  agreement at a selected total byte through later stores; it assumes no
  optional-map equality. Output is `Vsa.Machine.output` equality throughout;
  no raw `sailOutput` vector equality is inferred.

`InitializedString.Requirements` separates static geometry/footprints from
`Memory`'s current metadata/readable bytes. This lets the caller supply
geometry at entry and derive source bytes from the formatter's actual run.
The existing initialized-string interfaces and consumers still build.

Remaining caller conditions are explicit: the reachable native registers
and parsed `%ld` bytes; locale/tables, code pins and symbolic read ownership;
native read/write windows and executable/library separation; young pointer,
limit, nursery room/alignment and allocator metadata; metadata/code frames
through formatting; allocation/copy separation from source and original
save bank; and the selected owned-block footprint premise for `.live`.
After-call runtime invariants, heap placement/freshness/accounting and their
transport into a `caml_format_int`/C_CALL2 producer remain to be supplied.
This native summary does not discharge a complete primitive or C_CALL2.
General `GoodF1` remains unchanged: `d/i/u/x/X/o`, flags, width, precision,
large/major allocation and the second formatting/free path remain open.
`BarrierGrowthFull` stays G2; `CustomMemCall` stays named; C4 round 2 waits
for F1.

Validation on the resumed worktree:

- Guarded/capped `lake build
  OCaml.Vm.Primitives.Format.AllocSprintfNative
  OCaml.Vm.Primitives.InitializedString
  OCaml.Vm.Primitives.WriteLogObservation
  OCaml.Vm.Primitives.CamlSysExecutableName
  OCaml.Vm.Primitives.Format.VsnprintfCaller
  OCaml.Vm.Primitives.Format.FormatInt`: **1,412 jobs**, successful
  (`/tmp/sprintf-native-final-build.log`).
- Guarded/capped `lake env lean
  experiments/syi/alloc-sprintf-native-audit.lean`: **28 reports**, including
  every one of the **16 new theorems**, the four initialized-string
  compatibility theorems, `short_initialized`, four decoded call targets
  and three decimal facts. All depend only on `propext`, `Classical.choice`,
  `Quot.sound` (`/tmp/sprintf-native-final-audit.log`, checked for exact
  coverage/allow-list/registration in
  `/tmp/sprintf-native-final-audit-check.txt`). All 28 are registered
  in `OCaml/Audit.lean`; 18 registrations are new. Full Audit stays with
  the lead gate.
- Format, string-wrapper, vsnprintf-step and stdio-template generator checks;
  hole, discipline and abstraction gates; and `git diff --check` pass.
  Generated outputs are unchanged; C4 remains at 3
  (`/tmp/sprintf-native-final-checks.log`).

Every Lean invocation used `python3 scripts/lean-guarded.py --log /tmp/...
-- scripts/lean-capped.sh lake ...`, checked `free -g` first (available
≥25 GB), and ran alone under the inherited 12 GB cgroup/two-thread policy.
No proof budget was increased. The duplicate
`experiments/syi/sprintf-entry-prefix.lean` was removed only after comparing
it against `AllocSprintfEntry.lean`; all its declarations are retained there
and the scratch is preserved in checkpoint `5d6bc04f`.
Checked edits await lead review, commit and `scripts/integrate.sh`; no Git
metadata/landing queue writes or subagents were used.

## Initialized-string nursery return (2026-10-27): checked for lead review

Started at clean `5967f970`. Read `CLAUDE.md`, relevant `PHASES.md`/`PLAN.md`
and lane/dead-end sections, and ran `scripts/abs_inventory.sh` before proofs.

`InitializedString.initialized_string_nursery` proves the actual native
`caml_alloc_initialized_string` entry at `0x8000c284` through its original
caller return. Its `Input` consists of initial registers, `LeafInput`,
`VsaOk`, length/address bounds, native save/read windows, nursery room and
metadata, executable/library pins and concrete separation facts. No callee
execution or final postcondition is a premise. The source is an arbitrary
byte buffer; it needs no OCaml heap header, C sentinel or static provenance.
In particular, `AllocSprintfLong.short_initialized` uses the caller's native
stack buffer at `sp + 16`.

`gen_fn.py --ocaml-string-wrapper` now shares its CFG/block/call emitter
between the two string constructors and generates `InitializedStringSteps`
and the actual ELF code predicates. The decoded saves at `0x8000c284` save
ra/source/length; the allocation JAL at `0x8000c294` targets `0x8000c174`;
the argument loads start at `0x8000c298`, the memcpy JAL at `0x8000c2a0`
targets `0x80042848`, and the restoring return starts at `0x8000c2a4`.
The proof reuses `alloc_string_nursery` and `memcpy_summary` at those targets.

Common laws live beside the existing StringCopy producers:

- `callerLog`/`caller_readback_at` derive all three saved words from the
  actual preceding stores; `memcpy_readOnly_log` preserves source bytes
  and library code through nursery allocation, including a stack source.
- `TailBoundary`/`finish_tail` factor the argument loads, decoded memcpy call,
  copying, canonical-padding preservation and restoring native return.
  Its instances use each constructor's own generated native addresses.
- `CopyPostAt` retains the full header, bytes, zero padding and padding count,
  original stack/return, saved ABI registers, output and byte frame.
  `CopyPostAt.{object,padded,source}` in `Memcpy.lean` expose representation
  and source preservation. Shared `footprint`, `memory_complete` and
  `observed_log` provide complete total-byte effects; the existing copy-string
  APIs remain compatibility instances. Register composition uses `GprsSame`.

`AllocSprintfLong.short_continuation` is reused directly and now retains its
library/register frame. `short_initialized` composes that actual path from
`0x80013f10` through initialized-string allocation and back to `0x80013f20`,
with initial data/geometry requirements. `decimal_nursery_small` uses the
proved length ≤20, via `nursery_small_of_le20`. It is not a bound for arbitrary
GoodF1 formats and does not follow from Fits.

The decimal formatter prologue/wrapper, prologue-derived
`VsnLongEntry`/`SymbolicInput`, spills/readbacks and original native return
are now composed in the 2026-10-28 summary above. Still open: selected
ownership, nursery/runtime and separation suppliers at the actual reachable
call; after-call runtime facts;
`caml_format_int` and C_CALL2. General GoodF1 still includes `d/i/u/x/X/o`,
flags, width, precision and large/major results. `BarrierGrowthFull` stays
G2, `CustomMemCall` remains named, and C4 round 2 waits for F1.

Validation passes:

- `python3 scripts/lean-guarded.py --log /tmp/initialized-compose-build.log --
  scripts/lean-capped.sh lake build
  OCaml.Vm.Primitives.Format.AllocSprintfLong
  OCaml.Vm.Primitives.CamlSysExecutableName
  OCaml.Vm.Primitives.Format.VsnprintfCaller
  OCaml.Vm.Primitives.Format.FormatInt`: **1,403 jobs**, including every new
  module, the shared copy producers and their existing consumer closure.
- The same guard/capped wrappers with `lake env lean
  experiments/syi/initialized-string-audit.lean`: **81 reports**, all using
  only `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/initialized-string-audit.log`, independently checked by
  `/tmp/initialized-string-audit-check.txt`). All 63 previously unregistered
  reports are now in `OCaml/Audit.lean`, including every new theorem, both
  generated call targets and the two tail-boundary instances.
- String-wrapper and format generator `--check` pass. Hole, discipline and
  abstraction gates pass (C4 remains at 3); `git diff --check` passes.

Every Lean invocation checked `free -g` first (available ≥25 GB), used the
required guard and capped wrapper, and ran alone in this worktree with the
inherited 12 GB cgroup/two-thread policy. No virtual-address limit or proof
budget increase was used. The shared saved-bank readback elaboration dead end
is recorded in `DEAD-ENDS.md`; its final proof uses the explicit log shape.
Generated outputs were produced only through their generator.

Checked edits remain uncommitted for lead review. Full `OCaml.Audit`, commit
and `scripts/integrate.sh` landing remain the lead gate. No Git metadata or
landing-queue write, subagent, model guard or trust primitive was introduced.

## Plain LONGINT allocation composition (2026-10-27): checked obstruction

Started from clean committed `1ac28477`, including `8b1f1377`'s final
`VsnprintfLong` contract and caller witness. Read the binding briefs and
`DEAD-ENDS.md`, and ran `scripts/abs_inventory.sh` before proof work.

The requested direct `caml_copy_string` splice contradicts this ELF.
`AllocSprintf.copy_call_target`/`copy_call_decode` certify the JAL at
`0x80013f1c` to `0x8000c284` (`caml_alloc_initialized_string`). The existing
`StringCopy.copy_string_machine` summary starts at `0x8000c254`, with its
source in a0. The short path instead passes the decimal length in a0 and
the local buffer in a1. `AllocSprintfLong.copy_string_target_obstruction`
checks the target mismatch; `copy_string_argument_obstruction` independently
checks that the decimal length cannot equal that buffer pointer under the
ordinary stack bound. Neither theorem claims an unreachable caller or an
impossibility of proving the initialized-string path.

`AllocSprintfLong.short_continuation` composes the generated `fits_fast`,
`copy_fast` and decoded `call_registers_summary` through `summary_bind`.
It starts at the real vsnprintf continuation `0x80013f10` and executes to
initialized-string entry, retaining exact arguments, memory, native entry
facts and observable output. Its length premise is a data observation;
it assumes no callee execution or return. `decimal_fits` reuses
`intToString_length_le` and `ParseFormat.bltu_false_of_le`; `decimal_buffer`
extracts all decimal bytes and the final NUL from the checked `VsnResult`
with capacity 128, proving length ≤20 and fit including NUL.

**The plain decimal native milestone is now checked above.** The
entry-to-return `caml_alloc_sprintf` summary establishes
`VsnLongEntry`/`SymbolicInput` and the spilled argument from the prologue;
initial locale/data readbacks and code separation remain explicit conditions.
It does not supply a C_CALL2 producer. Its parsed
format remains at `sp + 240`, outside seven slots ending there, with
`snpAbove = 192`. Selected ownership, nursery capacity, allocator/runtime
metadata, native saved-word separation and after-call runtime suppliers
remain open; original return restoration is proved. No primitive-return
summary, selected ownership or raw Sail-output equality is inferred from
weaker observations.

Validation:

- `scripts/lean-capped.sh lake build
  OCaml.Vm.Primitives.Format.AllocSprintfLong
  OCaml.Vm.Primitives.Format.VsnprintfCaller
  OCaml.Vm.Primitives.Format.FormatInt`: **1,076 jobs**, including
  `AllocSprintf`, `VsnprintfLong`, `ParseFormatCall` and the copy-string
  dependency closure (`/tmp/bprime-sprintf-long-build2.log`).
- Focused `experiments/syi/alloc-sprintf-long-audit.lean`: **9 reports**;
  all use only `propext`, `Classical.choice`, `Quot.sound`
  (`/tmp/bprime-sprintf-long-axioms.log`). All five new theorem audits
  are registered in `OCaml/Audit.lean`; full Audit stays with the lead.
- Format, stdio-template and vsnprintf-step generator checks pass. Generated
  outputs are unchanged. Hole, discipline and abstraction gates pass
  (C4 remains at 3); `git diff --check` passes.
  Every Lean invocation used the capped wrapper,
  checked `free -g` first (available ≥25 GB), and ran one build at a time.

Checked edits remain for lead review, commit and `scripts/integrate.sh`.
No Git metadata or landing queue writes, subagents, proof-budget increases
or trust primitives were used. General `GoodF1` formatting still requires
`d/i/u/x/X/o`, flags, width, precision and large/major allocation.
`BarrierGrowthFull` remains G2; `CustomMemCall` remains a named premise;
C4 round 2 still waits for F1.

## F1 round (2026-10-05): entry, halt, final assembly

**Done**
- `OCaml/RefinementF1.lean`: the F1 domain `GoodF1` (`Good`, plus every
  reachable state decodes to an `InF1` instruction: an F1 opcode, and a
  `primsF1` name for C_CALLs), `GoodF1.of_static` (a static code check plus
  "reachable PCs decode"), and `OcamlrunRefinementF1` (same conclusion as
  `OcamlrunRefinement`, `GoodF1` for `Good`; implied by it, `OcamlrunRefinement.f1`).
- Assembly: `F1Arms P c0 R` is the arm table. It has `entry` and one
  `OpArm P R op` row per F1 opcode. Each row is stated over a loop invariant
  `R` the families choose (it may depend on `c0`, e.g. the native frame
  saved at entry). A row concludes `ArmOutcome R c (stepI P s i)`: `.next`
  means `Plus` into `R`, `.halt` means `Halts`. `ArmOutcome.of_next` and
  `ArmOutcome.of_cases` adapt existing `*_step_arm` bridges. `F1Arms.simR`
  and `ocamlrun_refinementF1_of_arms` give the headline, exposed as
  `Theorems.ocamlrun_refinement_F1_of_arms`. `ArmSim.f1Arms` shows that the
  old contract is the `Running` instance.
- `OCaml/Refinement.lean`: simulation by any relation, `SimR` /
  `run_simR` / `SimR.refines` / `refines_of_forward`. `run_sim`,
  `simOfArms` and `ocamlrun_refinement_of_sim` are now its instances, with
  the same statements.
- Why per-opcode rows carry both outcomes: one lemma "only STOP/C_CALL
  halt" over all of `stepI` hit the default 200k heartbeat limit, both via
  `split` on `stepI.eq_def` and via `cases op; simp only [stepI]`. With the
  opcode and argument shape concrete, a single opcode reduces in about 1 s.
  So each row discharges its own no-halt fact.

**Round 2 draft**: the previous session's unlanded WIP commit `7c68e6e`
(the 202-shard rules, function/loop/abs summaries; 2.5M generated lines)
fails stage a8. Its 7 new C4 hand proofs make C4 FLAT (see "Round 2"
below), and the F1 brief pauses B′ scale-up. It is NOT landed. It is kept
on the local branch `bprime-round2-draft`; `lane/bprime` was reset to
`origin/main`.

- Landed `be2742b`: the assembly above (full gate).
- `OCaml/Programs/F1Check.lean`: `runToF1` (runTo that also checks `InF1`
  decoding at every visited state) and `GoodF1.of_runToF1`. A halting
  checked run visits every reachable state, so `whileMin_goodF1` is one
  `decide +kernel` (27 s). `whileMin_halts_of_arms`: from `Loaded L whileMin c`
  and the F1 arm tables, `Halts c "55\n2500\n36\n" 0`. Its domain premises
  are discharged by `whileMin_goodF1`, `whileMin_fits` and `whileMin_gcSafe`
  (a6-gc).
- `OCaml/Vm/Sim/Invocation.lean`: `Invocation D c` is the native frame fixed
  at entry: x2 = nativeSp, the `Caml_state` pointer, and the bytes of
  `invocationRanges` = [sp, sp+32) ∪ [sp+200, sp+640). It excludes
  [sp+32, sp+192), where arm bodies spill. It is frame-shaped: arms preserve
  it from their write log alone, via `InvocationOutside` and
  `Invocation.frame`/`frame_log`/`frame_read`. Agreed with a1-arms: the F1
  invariant (since replaced by `Running.native`, see below).

- Landed `81ccb44`: F1Check and Invocation.
- The entry machine segments are generated (`gen_arm_pilot.py`) and build
  under the default limits:
  * `INTERP_ENTRY_SAVE`: 0x80001df8 → 0x80001e38, bnez taken; 7 s;
  * `INTERP_ENTRY_PREP`: → jal setjmp, loads named (opaque loads);
  * `SETJMP`: 0x80042c4c → ret; 10 s;
  * `INTERP_ENTRY_RESUME`: 0x80001e80 → 0x80001f40, beqz taken;
  * then the existing `LOOP_SETUP`.
  As one 33-step segment, the save and prep parts together hit the 200k
  heartbeat whnf limit; split in two they fit.
- `entry_save` (`OCaml/Vm/Sim/EntrySave.lean`): the prologue's exact
  13-store log, the new sp, preserved registers and the image, from the
  caller's frame. `EntryFrame`/`slot_nat`/`slot_tac` (`EntryFrame.lean`)
  normalize frame addresses once; every store premise closes by `omega`.
- `InterpCaller` (`OCaml/Vm/Caller.lean`), to become `LoadedAt.caller`: callee-saved registers with
  ra = 0x80004ff8, sp above `heapEnd`, caml_main's frame with its ra slot
  = 0x80001df0, the `Caml_state` record in the arena, and `PayloadOutside`
  of entry's write footprint. Without it, STOP's return is unconstrained
  and the statement is false. The captured whileMin cut carries it as an
  to be discharged for the closed captured whileMin witness
  (`WhileMin.loaded`) in the same commit that adds the field, so that witness
  stays closed. `InterpCaller.of_mem` transports it through `fillZero`.
- F1Loop is dropped. a1-arms moved the invocation into `Running.native`
  (`∃ D, Invocation D c ∧ NativeValid D`, with `NativeValid` as specified by
  bprime), so the table invariant is `LoopAt`.

- **`ArmSim.entry` proved** (`entry_loopAt`, `OCaml/Vm/Sim/EntryLoop.lean`).
  Starting from `LoadedAt L P c pl cp high`, the machine reaches
  `LoopAt L P P.init c'` at least one step later (all five `Running`
  fields). The run chains the generated segments:
  * `entry_save`: 13 callee-saved stores;
  * `entry_prep`: prog, `callback_depth + 1` and the four `Caml_state`
    saves, each load read back through the earlier stores;
  * `entry_setjmp`: 14 jump-buffer stores;
  * `entry_resume`: `external_raise = &raise_buf` and the initial VM registers;
  * `LOOP_SETUP`.

  The total memory effect is one `entryLog`, covered by `entryFootprint`
  (`entryLog_cover`). From that cover follow: the payload frame
  (`PayloadOutside.cover`), the primitive table, the runtime invariant via
  `WindowStable` on `entryWindows`, `StackGeometry.transport`, and the
  entry snapshot `NativePlaced`, whose `NativeValid` return slots are read
  back from the save log and caml_main's frame.

  Named premises: `InterpCaller` (now also the cut's dispatch clock and the
  primitive table's separation), `StackGeometry P P.init c pl cp high` at
  the cut, and `WindowStable L.runtimeOk (entryWindows …)`. All three become
  `LoadedAt` fields with their proof for the captured whileMin cut.

- **STOP halt** (`OCaml/Vm/Sim/Stop{Halt,Ready}.lean`):
  * `stop_do_exit_summary` discharges `StopDoExitSummary` with a1-prims'
    `do_exit_halts` (status 0; console unchanged; the quiet-exit globals read
    back through STOP's stores);
  * `stop_ready` gives `StopInvocation`/`StopCallerReady` from
    `Running.native` and the `Caml_state` placement;
  * `stop_exit_continuation` composes them for a1-arms'
    `stop_halt_step_arm`.

  Named premises: `StopExitReady` (ExitGlobals, caml_do_exit's 208-byte
  window, GPR presence and HTIF idle at caml_do_exit) and an ordinary accu
  word. The latter needs EvenPlace at mod 4 (requested from a1-arms) and
  `GoodF1.stopAccu` (new: STOP never returns a `.raw` word, which caml_main
  would read as an exception; `whileMin` still checks in one kernel run).

**ArmSim.halt complete (2026-10-06)**
- `ccall1Exit_pinned fits : CcallExit Gc.f1Layout P .C_CALL1 0`. Its
  `present` premise is discharged by `ccall1_present`: ra and a0 come from
  the setup, sp from the native invocation, and s0–s10 from a1-arms'
  `CcallSetupPost.calleeSaved`.
- The generator's FIXED `exit` now points at it, so `F1PremisesFor` has no
  `c_call1_exit` field. STOP and caml_sys_exit are the only halting F1
  outcomes, and both are proved.
- `g1_capacity` moved from the generated table to `Sim/G1Capacity.lean` to
  break the import cycle.

**caml_format_int and caml_ml_open_descriptor_out (2026-10-06, in progress)**
- format_int, `"%d"` path: `scripts/syi/ocaml_format.py` (`gen_fn.py
  --ocaml-format`, stage a5) emits block certificates and `_fast` wrappers.
  * Done: block families of parse_format, caml_string_length,
    caml_alloc_sprintf and caml_format_int. `string_length_call` is proved.
    `parse_format_call` (`ParseFormatCall.lean`) is proved: the whole
    function as a call summary, composed in four phases (`measure`, `copy`,
    `append`, `finish`). Its premises are `MeasureInput` (VsaOk, the global
    pointer, a 48-byte native frame, the placed format string apart from it),
    `BufferInput`, `2 ≤ n`, the buffer above the frame (`buf = sp` at
    caml_format_int's call), and the conversion test. The test is proved for
    all bytes by one kernel check (`plain_guard_all`).
  * `_svfprintf_r` on `%ld` (`Format/SvfLong.lean`): `svf_convL`,
    `svf_intL` and `svf_iterLD` are proved, alongside upstream's `%lld`.
    `IntAt` admits the LONGINT flag 16 (template change). Restored after
    41c1c810 dropped it in a rebase.
  * `vsnprintf` joins `snpText`: `retarget_stdio_specs.EXTRA_CODE`, its bytes
    in `snpCodeImg`, `LibraryText` regenerated. Its step table
    (`Format/VsnprintfSteps.lean`, all 47 wrapper instructions plus the two LONGINT rows) comes from
    `scripts/syi/gen_snp_extra.py`, ported from syi's `gen_interp_steps.py
    --target snp` (stage a5).
  * **Caller-layout generalization (2026-10-27, checked; lead review pending):**
    inherited output edits are migrated into the stdio templates and regenerated.
    `s` is a synthetic base: for vsnprintf's 224-byte frame, use `s = sp + 48`.
    `SnpGeom.d_sep` now permits a buffer above `s - 240` (past the formatter's
    frames and the FILE fields), including caml_alloc_sprintf's `sp + 16`.
    `snpS` owns bytes through `s + snpAbove` (`snpAbove = 192`). `ArgsOut`
    gives argument ownership, address bounds and separation from the exact
    `SvfW` writes; `ArgsOut.frames` exposes interval separation to `svf_mem`.
    It replaces `hap1`/`hap2` in the conversion and loop contracts, including
    `svf_fmt`, `loop_fmt`, `svfprintf_nw`, and LONGINT's `svf_iterLD`.
    `ArgsAt` still supplies the actual words; no execution premise is added.
    `ArgsOut.of_spill` adapts snprintf's original spill with its buffer above `s`.
    `VsnprintfLayout`/`vsnprintf_layout` state the concrete FILE at `sp - 216`,
    formatter entry stack at `sp - 224`, 128-byte buffer at `sp + 16`, and all
    seven argument slots at `sp + 184`; their only inputs are stack bounds
    and alignment. A concrete stack witness is in the focused audit file.
  * **Native plain LONGINT decimal wrapper (2026-10-27, checked; lead review pending):**
    `VsnprintfLong.lean:vsnprintf_long_symbolic` composes generated wrapper rows
    with `svf_entry`, `svf_iterLD`, `svf_iterEnd` and the native return epilogue.
    `VsnGeom` permits arbitrary destination/positive capacity below INT_MAX,
    with destination separation from the wrapper's saved bank. The prologue
    establishes the FILE pointer/count/flags from actual stores. `VsnResult`
    gives exact decimal length, `min length (capacity - 1)` bytes, the final
    NUL, original ra/sp and ABI saved registers, and owned bytes outside the
    formatter/wrapper stack and destination. `vsnprintf_long_summary` uses
    `symbolic_summary` and `SymbolicInput`/`VsaOk`; it assumes initial data,
    code and geometry, with no callee run or desired return post as a premise.
    `vsnprintf_long_memory` combines the owned-byte and local machine frames
    for every outside address; the local post also preserves observed output.
    The generator now owns the two LONGINT rows formerly written in SvfLong.
  * **Satisfiable checked caller:** `VsnprintfCaller.entry` constructs the
    complete data contract at `sp = 0x87fff000`, synthetic `s = sp + 48`,
    FILE `sp - 216`, buffer `sp + 16`, seven spill slots `sp + 184`, parsed
    format `sp + 240`, and the real return PC `0x80013f10`. It supplies native
    code, locale data, a spilled 42 and `VsaOk`; `returned` proves an actual
    `Steps` run to that PC, `a0 = 2`, original sp, bytes `4`, `2`, NUL and
    final `VsaOk`. This is a constructed entry-state witness, not startup
    reachability or the caller's own prologue execution. The shared template
    uses `snpAbove = 192`: all seven slots end exactly before the parsed
    format, so the native bridge's read-only separation is satisfiable.
  * **Still open:** derive `VsnLongEntry`, `SymbolicInput` and separation
    from the reachable `caml_alloc_sprintf` caller, and compose its actual
    240-byte prologue/spills with the native summary. The explicit initial
    locale/data facts are not yet supplied from the F1 runtime invariant.
  * Compose caml_alloc_sprintf's 240-byte frame and varargs spills with that
    summary; for the short-result path prove the result fits 127 bytes and
    compose `caml_alloc_initialized_string` (`alloc_string_nursery` + memcpy),
    including fresh bytes, readiness, return and memory/register frames.
    The long-result path remains open: `caml_stat_strdup` of the format,
    `caml_alloc_string`, a second `vsnprintf`, `caml_stat_free`, and return.
    General large results also require the normal `caml_alloc_shr` tracking
    wrapper, `caml_check_urgent_gc`, and any required major-heap expansion;
    the existing exact-size/least-large-block milestones alone do not supply
    these for every result admitted by Fits. Plain `%ld` has length at most
    20; that fact must not become a bound on general GoodF1 formatting.
  * Compose parse_format, the tagged-integer conversion, allocation and return
    for caml_format_int, then discharge its C_CALL2 representation/effects
    adapter. Its exact target is
    `PrimReturnsAtR Gc.f1Layout P .C_CALL2 0x80003004#64 1 "caml_format_int"`:
    from Reach/CcallReady, the successful primF1Impl equation, the resulting
    heap budget and CcallSucc, produce CcallCallee and its CcallReturn summary,
    including represented result/allocation, runtime readiness, caller saves,
    payload/bindings/world and native/output frames. The general
    `F1CcallOpen.format_int_c_call2` field stays open:
    `formatInteger` accepts `d/i/u/x/X/o`, flags, width and precision. A plain
    `%d` → `%ld` result does not cover that domain. No C4 scale-up is started.
  * The native bridge consumes `VsaOk`, including all 31 GPRs present,
    code-byte presence and idle HTIF. The constructed caller supplies it;
    the reachable-call adapter must derive the complete library input from
    its actual setup and runtime representation.
  * `emit_fast` fixes: lbu window loads read one byte; opt-in `shiftAddr`.
  * Callees: memmove through a2-sem's `memmove_call` (in flight), strlen
    through `strlen_call`, caml_alloc_string through a1-prims'
    `alloc_string_nursery`, memcpy through `memcpy_summary`.
  * vsnprintf `%ld` is a LONGINT variant of upstream `svf_iterLLD`.
  * Validation (2026-10-27): `scripts/lean-capped.sh lake build
    OCaml.Vm.Primitives.Format.VsnprintfLong VsaIris.Vsa.SnpFmt
    OCaml.Vm.Primitives.Memmove` passed (978 jobs), then
    `scripts/lean-capped.sh lake build OCaml.Vm.Primitives.Format.VsnprintfCaller`
    passed (963 jobs). These rebuild all affected stdio/format modules at
    default proof budgets under the inherited 12 GB cap and two Lean threads;
    free memory was checked before every build. Build logs are
    `/tmp/bprime-vsn-build4.log` and `/tmp/bprime-vsn-caller-build6.log`.
    `scripts/lean-capped.sh lake env lean experiments/syi/vsnprintf-long-audit.lean`
    passed: all 34 reports use only `propext`, `Classical.choice`, `Quot.sound`
    (or none); log `/tmp/bprime-vsn-axioms.log`. All new public theorem audits
    are registered in `OCaml/Audit.lean`; its full build stays with the lead.
    `python3 scripts/retarget_stdio_specs.py --check` (47 modules),
    `python3 scripts/syi/gen_snp_extra.py --check` (49 instructions), the hole,
    discipline and abstraction gates, Python syntax compilation, and
    `git diff --check` pass. Checked edits are left for lead review and
    `scripts/integrate.sh`; Git metadata and the landing queue were not written.
    BarrierGrowthFull remains with G2, CustomMemCall remains a named premise,
    and C4 round 2 waits for F1. The general format_int field and major string
    allocation obligations are unchanged; no nursery bound is inferred from Fits.
  * Lead integration repair (2026-10-27): the expanded `snpS` window made
    the zero-base `memmove` bridge require explicit RAM lower bounds.
    `snpText_bounds` reuses `forall_piecesText`; the bridge also uses
    `MoveGeom.s_lo` and unfolds `snpAbove`. Its contract is unchanged.
    The focused Memmove build passes (964 jobs), and all four affected
    public theorem audits use only the standard axioms. Full gate rerun
    remains pending.
- Channel opening, `caml_ml_open_descriptor_{in,out}` (both bprime's since
  2026-10-12; they differ only by the output store `max := NULL`):
  * `scripts/syi/ocaml_channel.py` (`gen_fn.py --ocaml-channel`, stage a5)
    emits block certificates for:
    - `lseek`, `_lseek_r` and htif.c's `_lseek` (non-file path);
    - `caml_open_descriptor_in`, with both list-head outcomes;
    - both primitives.
    Its opt-in `logFacts`/`addrFacts` close `auipc`/`lui` literals in
    `emit_fast` without changing other modes' output.
  * `lseek_call` (`Channel/LseekCall.lean`) is proved: lseek on a descriptor
    that is open and not a file (`SeekFd`) returns -1 (ESPIPE) with an exact
    write log (`seekLog`); `htif_lseek` is its `_lseek` part. This is BcSem's
    `openChan` offset (-1 for streams).
  * `open_descriptor_in` (`Channel/OpenDescriptorCall.lean`) is proved, in
    three phases with named posts:
    - `open_allocate`: prologue and the checked `caml_stat_alloc(65616)`;
    - `open_seek`: `fd`, `enter_blocking`, `lseek_call` (-1), `offset`,
      `leave_blocking`, framed by `seekWindows`;
    - `open_link`: record initialization (`recordInitLog`), the old head's
      `prev` when there is one, the list head, the epilogue.
    `OpenedIn` gives `HeapReady ((record, 65616) :: H)`, `StaticKept`
    (every runtime global except the allocator's and the list head reads the
    same, so `ConsoleRuntime` and `SeekFd` carry over) and a byte frame
    outside `openWindows` and the allocator's footprint. Entry premises
    (`OpenInput`): `ConsoleRuntime`, `SeekFd fd`, the old head a word-aligned
    live block. stdin's `SeekFd` is not in `ConsoleRuntime` yet (a0-boot).
  * `OpenedIn` also gives the record's bounds, 16-byte alignment and
    freshness against `H` (`low`/`high`/`align`/`fresh`), the facts a6-gc's
    `LibHeapAt.link` consumes.
  * `ml_open_descriptor_out` (`Channel/MlOpen.lean`) is proved at the
    machine level, composed in three phases (`out_enter`, `out_flags`,
    `out_done`) around `open_descriptor_in` and `caml_alloc_custom_mem`.
    - Premises: `OutInput` (`open_descriptor_in`'s, one 16-byte frame
      down, so `NativeFrame sp 592`), a6-gc's site-generic
      `Gc.CustomMemCall Ready state` with `Ready (k + 1) c`, and
      `OutNursery H chs c` (`Caml_state` and the minor heap covered by `H`,
      the open records apart from `Caml_state`, nursery room for the
      24-byte block). `out_nursery` builds it from `LibHeapAt` and the
      young-pointer bounds.
    - The call site is `outSite (sp − 16) record` (link `0x80015fa0`).
      `Ready` is framed from `c` to the call through `CallerApart`
      (`static`, `free`, `records`): the runtime's state is apart from the
      opening's save, malloc and flag stores. The young fields are kept
      because `Caml_state` is a live block apart from the record. After
      the call, `kept` gives the caller frame, the record and the list
      head, and `Ready k` survives `Channel(res) = chan` (the block is in
      the minor heap, apart from `state`).
    - Post (`OpenedOut`): the record's words as `ChanAt` reads them
      (`OutRecord`: fd, offset -1, end, curr, `max = NULL`, next,
      refcount 1, flags 4), `OpenChannelsLinked c d record`,
      `Channel(v) = record`, the ops word, the call's
      `Gc.CustomMemReturned` (block at young − 16, `∃ H' cap', HeapReady`)
      and `Ready k d`.
  * The summaries take any library live set (`OpenInput live …`, over
    `stat_checkedL`), so the adapter uses `imageLive`. `out_input` builds
    `OutInput` from `Gc.LibHeapAt` (charge 65616, `recordsAligned` for the
    old head), the C_CALL entry facts and `ConsoleRuntime` (stdout/stderr's
    `SeekFd` by `ConsoleFd.seekFd`), with `chs.length < maxChannels` a
    premise.
  * Adapter plan (`prim_caml_ml_open_descriptor_out_returns`):
    - Named premise `OpenOutRuntime L` (agreed with a6-gc, who discharges
      it for `f1Layout` together with `CustomMemCall`): `Ready`/`state`/
      `custom`, `budget` (the major-slice open premise) and `after`, which
      maps `LibHeapAt` at the entry plus the whole `OpenedOut` to
      `L.runtimeOk` at the return.
    - The frame is not a write log (newlib's free space and `state` are
      predicates), so the return uses `BarrierState.keep_field_step`'s shape:
      * an intermediate config `cm := writeLog c openLog` copies the
        return's bytes on the observed windows the primitive changes (the
        record, the old head's `prev` word, the list head, the block, the
        `young_ptr` word);
      * at `cm`, the log-based lemmas build `VmPayload`/`LoopGeometry` for
        the opened state under `cp.put n record`;
      * the `keep` lemmas (`VmPayload.keep`, `LoopGeometry.keep`,
        `bindings_keep`, `Invocation.keep`) carry them from `cm` to the
        return through `OpenedOut.kept`.
    - Entry: `StringAllocEntry.of_setup` (native stack and nursery room), `out_input`
      and `out_nursery` from `LibHeap` (`F1Pins.libHeap` through `after`'s
      premise), `openChan_bound` and `openChan_fresh` from the equation.
  * Adapter pieces landed (`Sim/{PrimOpenOutReturns,OpenGeometry,PayloadObserved,OpenPayload,OpenOutFrame}.lean`):
    - `OpenOutRuntime L` and `open_out_entry`: from the C_CALL setup,
      `LibHeapAt` over `placedChannels cp n` (`OpenChannels.unique` against
      `channelsListed`), `OutInput` on the native stack, `OutNursery`, and one
      quiet custom allocation. The console descriptor (`v = 3 ∨ v = 5`) is
      still a hypothesis (below).
    - `LoopGeometry.openChan` (+ `StackGeometry`/`NurseryGeometry`): the
      geometry across the opening, from the new record's separation
      `NewChannelPlaced` (heap unchanged; the custom block is the separate
      `alloc` step).
    - `PayloadObserved`: the bytes `VmPayload` reads, with the records split
      around their link words. `VmPayload.keep_observed` carries the payload
      across them, and the barrier's `VmPayload.keep` is now its instance.
    - `VmPayload.openChan`: the payload of the opened state (`openedSt`),
      from a kept payload, the custom block's layout and the new `ChanAt`.
    - `covered_kept`, `record_kept`, `domainField_kept`, `static_kept`:
      `OpenedOut.kept` discharged per class of observed byte. Two cases are
      excluded: `young_limit` (it is next to `young_ptr`, whose kept premise is
      word-sized) comes from the call's `youngLimit`, and `young_ptr` itself
      is the allocation.
    - `CcallSucc`/`PrimReturnsAtR` (a1-prims' option (b), taken by bprime):
      `CcallReturns.callee` passes the successor's reachability, so
      `open_out_console` gets fd ∈ {1, 2} on a stream from `GoodF1.consoles`.
      `PrimReturnsAt.toR` lifts the other adapters unchanged.
    - `open_out_observed`: every `PayloadObserved` byte is kept.
      `open_out_placed`: the record's `NewChannelPlaced`.
      `open_out_geometry`: the loop geometry at the return (alloc to a
      config with only `young_ptr` written, then `openChan`).
    - `caml_format_int` was sequenced after `open_descriptor_out` (bprime's
      own option 2, not a decision by Kiran); it is on whileMin's critical path
      (its C_CALL2 sites) and is bprime's current item.
  * **`prim_caml_ml_open_descriptor_out_returns` is proved** (`Sim/OpenOutReturn.lean`), a
    `PrimReturnsAtR` at every C_CALL opcode, arity and return site.
    - Premises: `OpenOutRuntime L` (`∃ Ready state, OpenOutRuntimeAt`;
      a6-gc discharges it for `f1Layout` with `CustomMemCall`) and
      `ConsoleChannels P` (`GoodF1.consoles`).
    - Assembly (`open_out_return`): `Ccall1Saved` (statics, `extern_sp`,
      the VM stack's env slot), bindings (`primTable_kept`), `NativePlaced`
      (`native_kept`, `external_raise`), `LoopRegisters` (x19–x27 by
      `keep_upper`, presence and `gp` by `OpenedOut.gprs`, HTIF idle), the
      payload and geometry of the opened state, and `PlatformOk` through
      `after`. The output is kept through every phase (`OpenedOut.output`).
    - whileMin's table field is now `openOutRuntime : OpenOutRuntime
      Gc.f1Layout` (`gen_f1_table.py` reads the `R` form and lifts the other
      summaries by `.toR`).

  * `omega` exhausts the recursion depth on chained literal subtractions
    (`s - 32 - 544`) and on some goals with the arena bounds unfolded;
    `arena_omega` normalizes `Nat.sub_sub` and generalizes the bounds first.
- open_descriptor_out obligations, status:
  * Supplied by `OpenedOut`/`OpenedIn`:
    - the `ChanAt` words (`OutRecord`), with 16-byte alignment;
    - `OpenChannelsLinked`, `HeapReady ((record, 65616) :: H)`;
    - `fresh`, and the byte frame for `keepTable`/`keepLinks`.
    So a6-gc's `Gc.LibHeapAt.link` has every input; `chs.length < 64` comes
    from `openChan_bound`.
  * The StackGeometry channel-apartness fields are derived in the adapter
    (`open_out_placed`, from `fresh` and the covered regions).

**F1 input is stdin (2026-10-20)**
- `GoodF1.stdins : StdinChannels P`: every open input channel is fd 0 on the OS
  stdin stream. `consolesOk` checks it alongside the output channels (option (a),
  agreed with a2-sem), so `runToF1` and `St.shapeOk` are unchanged in shape.
  File input (ocamlc's `open_in`) is outside F1, ledgered in `Fragment.consoleLedger`.
- `caml_ml_open_descriptor_in` (bprime): **proved** as
  `prim_caml_ml_open_descriptor_in_returns`. The composition is generic over
  `Channel.OpenCode` (entry, call links and the three phase summaries per
  direction: `openOutCode`, `openInCode`; `OpenRecord out`, `chanFlagsLog out`),
  and both adapters share `prim_open_tail`. The phase lemmas of both
  directions (`{out,in}_{enter,flags,done}`, `flagsLog_eq_{out,in}`) are
  generated into `Channel/OpenPhases.lean` by `scripts/gen_open_phases.py`
  (stage a5 `--check`), between `MlOpenDefs.lean` and `MlOpen.lean`.
- The machine side shares MlOpen's composition (only `max := NULL` differs). The descriptor's `SeekFd 0` comes
  from a0-boot's coming `ConsoleRuntime.stdinSeek` (stdin is HTIF kind 1, so
  `ConsoleFd 0` cannot hold).
- `openChan`'s 64-channel bound is an F1/G1 scoping guard, not interp.c
  behaviour (`Fragment.channelLedger`; foreman).

**F1 output is console output; primitive split (2026-10-06)**
- `GoodF1.consoles : ConsoleChannels P`: in every reachable state, every open
  output channel has fd 1 or 2, an OS stdout/stderr stream, and a live
  process (`ConsoleChan`).
  * Why: a1-prims' flush/output summaries need it, and the machine certifies
    only HTIF's console descriptors.
  * a2-sem rejected a BcSem guard because the ocamlc differential writes
    files, so file output is excluded in GoodF1 instead (`Fragment.consoleLedger`).
  * Checked by `consolesOk` (`consolesOk_sound`), in `runToF1` and, for
    whileMin, in `St.shapeOk`.
- Primitive split with a1-prims (recorded in docs/lanes/a1-prims.md):
  * bprime takes `caml_format_int` (C_CALL2) and `caml_ml_open_descriptor_out` (C_CALL1);
  * a1-prims keeps flush, output_char and output;
  * fresh_oo_id was done by a1-prims.
- format_int plan: `parse_format` turns `"%d"` into `"%ld"`. newlib
  `_svfprintf_r` takes the LONGINT branch for it. ship-your-interpreter's
  `svf_iterLLD`/`loop_lld` (QUADINT, `"%lld"`) is the template; the retargeted
  copy here (`svfprintf_nw`) has only `%s` and 32-bit `%d`.

**GPR presence, entry side (2026-10-06)**
- `InterpCaller.gprs : GprPresent c.σ`, proved at the captured cut
  (`WhileMin.cut_gprs`, one key check per register in the generated table).
- `GprPresent.of_stepFrame` and `written_of_pins` (`EntryFrame.lean`) carry
  presence through a generated segment's `StepFrameOut` and output pins.
- Each entry post (save, prep, setjmp, resume) carries `gprs : GprPresent before → GprPresent after`, and so do
  `LoopSetupPost.gprs` and `EntryNativePost.gprs`.
- a1-arms consumes `EntryNativePost.gprs` for `LoopRegisters.gprs`. That
  discharges `ccall1Exit_f1`'s `present`.
- a2-sem asked for `Caml_state->external_raise = &raise_buf` at the loop head
  (DIVINT/MODINT's raise). This became `Invocation.externalRaise`; a2-sem
  landed both the arm side and the entry half (entryLog index 33), in 27b71b45.

**ArmSim.halt at C_CALL1: caml_sys_exit (2026-10-06)**
- `ccall1Exit_f1 (fits) (present) : CcallExit Gc.f1Layout P .C_CALL1 0`
  (`CcallExitF1.lean`). It runs a1-arms' `c_call1_exit_arm`, then a1-prims'
  `caml_sys_exit_halts`, which exits through caml_do_exit to the HTIF halt.
  The exit runtime comes from the invariant:
  * quiet-exit globals from `f1Runtime`;
  * HTIF idle from `LoopRegisters`;
  * the 224-byte window from `NativeValid.headroom`.
- Named premise `present`: the GPRs caml_do_exit reads are present at the
  callee entry. s7/s10 are pinned nowhere today; a1-arms is adding
  `LoopRegisters.gprs` (GprPresent), which discharges it via
  `CcallSetupPost.input.loop`. Then the generator passes `ccall1Exit_f1` for
  the table's `c_call1_exit` field. Halt is then complete: STOP and
  caml_sys_exit are the only halting F1 outcomes.

**InF1 minor-heap bound; whileMin's C_CALL returns (2026-10-06)**
- Foreman decision: MAKEBLOCK with `wosize > Max_young_wosize` (and CLOSURE /
  CLOSUREREC whose block exceeds it) take interp.c's `caml_alloc_shr` path and
  are outside F1. `InF1.minor : i.minorAlloc = true` (`RefinementF1.lean`,
  interp.c's own tests); ledger `Fragment.majorAllocLedger`. Rows get the
  bound from `InF1` (OpArm's premise), so BlockSizes/ClosureSizes retire.
- `CcallReturns.of_names` / `.of_primsF1` (`CcallNames.lean`): `CcallReturns`
  from per-primitive summaries `PrimReturnsAt` (a1-prims' adapters). The
  general instance needs no per-program premise.
- whileMin: `St.callNamesOk` joins the one shape run; `whileMin_ccallReturns`
  (`WhileMinCalls.lean`) uses its 7 primitives. `WhileMinOpen` is now 4
  fields: `setglobal_barrier`, and `c_call{1,2,4}_prims` (PrimReturnsAt for
  each of `whileMinCalls`).

**Deferred (2026-10-06)**: `Invocation.raiseBuf`
(`Caml_state->external_raise = D.nativeSp + raiseBufOffset`). Only the general
C-raise path needs it (a2-sem's zero-divisor row for programs that do divide
by zero), and it costs a frame hypothesis at ~90 native-frame sites (a1-arms).
whileMin does not need it: its divisors are never zero
(`whileMin_divisorsNonzero`). Entry's readback recipe, should it be added:
`word_writeLog_at` on `entryLog` at index 33 (the resume store).

**whileMin's open premises, generated (2026-10-06)**
- `WhileMinTable.lean` (generated with F1Table by `scripts/gen_f1_table.py`):
  `whileMin_halts_open (o : WhileMinOpen) : Halts WhileMin.cut "55\n2500\n36\n" 0`.
  Fields of unreached opcodes are discharged from `whileMinOps`; fields
  proved by the shape run are filled. As rows land and the generator reruns,
  `WhileMinOpen` shrinks. Currently it has 10 fields:
  * `row_CLOSURE`, `row_MAKEBLOCK` (a1-arms);
  * `setglobal_barrier` (caml_modify, a6-gc);
  * `c_call{1,2,4}_{returns,effects}` (a1-arms/a1-prims);
  * `scratch` (GPR presence in LoopRegisters, a1-arms).

**whileMin's remaining premises (2026-10-06)**
- `f1_table_for keep`: rows of opcodes a program never reaches are vacuous
  (`OpArm.of_unreached`), and premises are guarded by the kept opcodes.
- `whileMin` reaches 50 opcodes (`whileMinOps`). `whileMin_ops` and
  `whileMin_goodF1` now come from a2-sem's single shape run (`St.decodedOk`
  in `WhileMinShape.lean`); the separate `runToF1` kernel run is retired.
- `whileMin_halts_f1 (pre : F1PremisesFor (whileMinOps.contains ·) whileMin)`
  needs 16 fields:
  * proved by a2-sem's run: `extra`, `values`, `trapBounded`, `raises`;
  * open:
    - `row_CLOSURE`, `row_MAKEBLOCK`, `row_MAKEBLOCK2` (a1-arms);
    - `setglobal_barrier` (caml_modify, a6-gc);
    - `c_call{1,2,4}_{returns,effects}` (a1-arms/a1-prims);
    - `scratch` (MULINT/MODINT library scratch) and `modint_zero`.

**F1 assembly (2026-10-06)**
- `f1_table` (generated by `scripts/gen_f1_table.py`, drift-checked at a5):
  `Loaded Gc.f1Layout P c → GoodF1 P → Fits g1Budget P → F1Premises P →
  F1Arms P c (LoopAt Gc.f1Layout P)`. It dispatches all 134
  F1 opcodes to their rows; `F1Premises` collects the rows' program-level
  premises and the 15 rows still open (PUSHENVACC, GRAB, CLOSURE, CLOSUREREC,
  SETGLOBAL, MAKEBLOCK*, GETFIELD, SETFIELD*).
- `ocamlrun_refinement_F1_pinned` (the F1 statement for the pinned layout) and
  `whileMin_halts_f1` (the captured cut halts with "55\n2500\n36\n", exit 0),
  both from those premises (`F1Headline.lean`).
- `StackCapacity Gc.g1Budget` was false (8·3840 + 2·2048 = 34816 > 32768).
  a6-gc lowered the budget to 3584 stack words; `g1_capacity` is now proved.
- whileMin already has `ValuesInRange`, `BranchInts`, `ExtraBounded` and
  `TrapBounded`. Remaining whileMin premises: RaisesCaught, SwitchExotic,
  BinaryLibScratch, the DIV/MOD zero paths, FieldWriteReady, the C_CALL
  contracts, and the 15 open rows.

**Open / next** (2026-10-06, later)
- **Entry done for the pinned layout**: `f1_entry` (`EntryF1.lean`) takes
  `Loaded Gc.f1Layout P c` to a loop head representing `P.init`.
  * `LoadedAt` carries `caller` (InterpCaller) and `geometry` (ArmGeometry).
  * The closed whileMin witness fills them from a0-boot's
    `WhileMinCaller` and a6-gc's nursery geometry (`WhileMinLoaded.lean`).
  * `f1_entryStable`: entry's windows miss the F1 runtime footprint, after
    a6-gc carved out `caml_callback_depth`.
- **STOP row done**: `stop_row_f1 : GoodF1 P → OpArm P (LoopAt Gc.f1Layout P) .STOP`.
- Next: the F1 table assembly over a1-arms'/a2-sem's rows. C_CALL exit
  outcomes come through a1-arms' `CcallEffects` with a1-prims'
  `caml_sys_exit_halts`. Then `ocamlrun_refinement_F1_Statement Gc.f1Layout g1Budget`
  and the whileMin `Halts` (`whileMin_halts_of_arms` + `Gc.whileMin_loaded_f1`).

## Status

The proof/build exit criteria are met: all 23,678 backend instructions have
building generated rules, and `jumpStop_adequacy` instantiates
`bytecode_adequacy` on a generated function summary. Allocation and locality
milestones landed via `scripts/integrate.sh` as `a4d7b7a` and `65da6fc`;
both full gates passed. The generated-rule milestone uses the same full
integration gate. No lane proof/build obligations or user decisions remain.

## Proved

- `Heap.get_alloc_old`, `Heap.get_alloc_fresh`, `field_alloc_fresh`,
  `field_alloc_old` (`OCaml/Logic/Symbolic.lean:26`): allocation preserves old
  locations and exposes the new block, including infix fields.
- `closure_capture_read` (`OCaml/Logic/Symbolic.lean:59`) and the generated
  `capture_summary` (`OCaml/Programs/Generated/Demo.lean`): CLOSURE/GETFIELD2
  captures and retrieves any accumulator on an arbitrary heap and stack.
- `Run.iter_eq_of_agree` and `Run.iter_ok_of_step` (`OCaml/Run/Local.lean`):
  local agreement and partial simulation through the adopted run kernel.
- `decodeAt_local`, `code_extract_word`, `decodeAt_extract`,
  `CodeSlice.iter_eq`, `decoded_run_sound` (`OCaml/Logic/CodeSlice.lean:22`):
  instruction extraction and run locality with absolute PCs. The last
  instruction may leave a window; saved PCs and closure pointers are unchanged.
- `CertifiedBlock.decode_sound` and `CertifiedBlock.run`
  (`OCaml/Logic/Block.lean:29`): checked decoder entries lift a successful
  symbolic window run to the real program. A named `pin` premise states the
  exact extracted words required of the surrounding program.
- `call_summary`, `tail_summary` (`OCaml/Logic/Application.lean:28`): compose
  generated call prefixes, full-state application summaries and continuations.
  `apply1_enter`, `return_over`, `grab_under`, `restart_partial`
  (`OCaml/Logic/ApplicationSteps.lean:18`) reduce the real application arms.
  Summary predicates retain extra arguments, environment and caller frame.
  Back edges use the existing `loop_rule`; function termination/postconditions
  remain the client program proof's work.
- `jumpStop_summary` is generated through `runbc --lean` and instantiated via
  `jump_runFact`, `jump_wp`, `jump_hyp`, `jumpStop_adequacy`
  (`OCaml/Programs/GeneratedAdequacy.lean:12`). The last theorem invokes
  `bytecode_adequacy` with proved ownership and WP, leaving no client premise.
  This is a small branch/STOP fixture, not a proof of compiler termination.
- `pc_eq_of_reg` and `pc_alias_excluded` (`OCaml/Logic/BcModel.lean:95`):
  `bcModel.ok` now bounds the natural PC by 2^64. This makes the 64-bit PC
  ghost cell usable without aliasing; initial states satisfy the bound.

## Generated coverage and reproduction

`python3 scripts/gen_bc_rules.py` cross-checks host OCaml 4.14.4 dumpobj
instruction boundaries/opcodes against the vendored executable's CODE.
Closure entries delimit function regions; control-flow targets, transfers,
calls and 16-instruction cuts delimit windows. Signed operands come from
CODE. Every instruction appears in exactly one block. One lookahead word
supports decoder locality but is not an executable site.

| Module | Instructions | Blocks | Function regions | Measured wall | Peak RSS |
|---|---:|---:|---:|---:|---:|
| Translcore | 4,741 | 1,004 | 99 | 75.33 s | 1,505,620 KiB |
| Matching | 12,175 | 2,792 | 386 | 243.75 s | 3,204,964 KiB |
| Bytegen | 4,759 | 1,113 | 68 | 235.05 s | 1,577,300 KiB |
| Emitcode | 2,003 | 505 | 32 | 38.55 s | 988,696 KiB |
| Total | 23,678 | 5,414 | 585 | | |

Builds use default heartbeats and a 24 GiB cgroup, one lake build at a time.
Timings include shared-machine contention. `scripts/measure_bc_rules.py`
rebuilds only the selected generated modules and records source hashes,
wall/CPU time and peak RSS. Generated rules are checked at a5, and
`scripts/check_bc_audit.py` audits every generated block theorem against the
manifest. The root audit covers all handwritten headline theorems and the
end-to-end example. `scripts/gen_bc_demo.py --check` checks the fixtures.

The rules accept a code-window pin and a successful symbolic local run.
They certify the actual instruction semantics without inventing behaviour
for unsupported opcodes. Per-function semantic specifications, source-level
compiler correctness and growth of BcSem's fragment belong to subsequent
program proofs / other lanes.

## Evidence and integration

- A broad simplifier across an unresolved instruction reached the default
  200,000 heartbeat limit. Restricting reduction to the decoded instruction
  fixes it; no budget was raised.
- PC ghost encoding aliases 0 and 2^64; `pc_alias_excluded` checks the reason
  for the new `ok` bound. No BcSem transition was changed.
- Census correction: the compiler has 655,922 words and 412,087 instructions
  (VALIDATION.md:243); the lane brief calls the instruction count words.
- All four measured builds passed. Measurements and source hashes are saved
  in `results/bprime_build.json`. Final landing uses `scripts/integrate.sh`,
  including the generated-rule audit and full a1–a8/t1 gates.

## Fixed-address embedded-image migration (2026-10-01)

The foreman announced that a0-boot will move the embedded program to a
fixed-address `.embed` section and regenerate native data/code pins. Any
native data address used by this lane must come from `OCaml/Vm/Layout.lean`.
The bytecode generators and logic currently contain no native data addresses:
their PCs are CODE word indices. The hexadecimal constant in `gen_bc_demo.py`
is an OCaml Marshal format marker, not an address.

Initially rebased onto main `a22f2b9`; integration then caught up through
`772e509`, including the expanded BcSem definitions and audit import closure.
Landed the address audit as `bce2437` through `scripts/integrate.sh`: all
a1–a8/t1 stages passed, including 784 headline theorem audits and all 5,414
generated block-rule audits. Reran `scripts/gen_bc_rules.py` and
`scripts/gen_bc_demo.py` after that landing; both artefact sets are unchanged.
The image migration is not in that revision, so its follow-up remains open.
After the migration lands, rebase again, rerun both generators, and validate
through `scripts/integrate.sh`. Native Layout/decode/pin regeneration belongs
to a0-boot's migration landing.

## Round 2: stopped at the required abstraction gate (2026-10-02)

**Discovery round required before further C4 proof expansion.** Running
`python3 scripts/check_abstraction_gate.py` after registering the new hand
proofs produced:

```
C4-bytecode-specs: 10 hand proofs, first-quarter mean 7.5 lines, last-quarter mean 18.0: FLAT
gate: cluster(s) C4-bytecode-specs reached 8 hand proofs without the per-case cost falling by a third — run /abstraction-discovery
```

The seven added census entries are `length_loop`, `length_application`,
`abs_runFact`, `abs_haltFact`, `abs_wp`, `abs_hyp`, and
`compiler_abs_adequacy`, alongside the three existing CountLoop entries.
The lane brief explicitly requires stopping for a separately run discovery
round. Proof expansion has stopped. The gate has not been bypassed; Round 2
exit is **not met**, and the proof changes below are a preserved local draft,
not landed proofs. This log is being landed separately so the foreman can
see the obstruction without accepting proof changes that fail a8.

Completed and locally checked before the gate fired:

- Rebased through `1cfce0b`, including fixed `.embed` migration `7fa1750`;
  reran existing bytecode generators, with unchanged artifacts. Native data
  addresses still come from Layout; this lane introduces none.
- `gen_bc_all.py`: exact coverage of 412,087 instructions / 655,922 CODE
  words in 202 shards (limit 2,048 instructions), with 92,543 block rules.
  This includes initialization and the final STOP. `decodeAt_extract_tight`
  fixes the unnecessary lookahead requirement for fixed-length instructions.
- `gen_bc_functions.py`: conservative CFG census of 11,292 closure entries;
  all 6,172 generated normal/over/under application-case theorems built and
  passed standard-axiom audits across 47 shards. Per-shard measurements are
  in the draft `results/bprime_functions_build.json`.
- `gen_bc_loops.py`: both matched length-accumulator loops (entries 8372 and
  20141) built. `length_loop` uses `loop_rule` and a finite `ListSpine`
  invariant; generated summaries return the initial count plus spine length,
  preserving heap/world and restoring the caller frame.
- `gen_bc_abs.py`: finds actual Stdlib.Int.abs at CODE words [12349,12360),
  copies those bytes unchanged into a runbc-generated harness, and proves a
  functional `absWord` postcondition for every signed machine integer.
  `CompilerFunctionAdequacy.compiler_abs_adequacy` builds through
  `bytecode_adequacy`; `harness_run` proves the returned value is seven on -7.
  This is a compiler-helper harness, not termination of boot/ocamlc.
- `bcModel` adds the missing extra-argument representation bound; the
  draft `extra_alias_excluded` checks why ghost-word zero alone cannot rule
  out over-application at `extra = 2^64`. The earlier adequacy fixture builds
  with the strengthened bound.
- Draft coverage: 285/11,292 normal function summaries (2.52%), 282 over
  cases, 5,608/5,608 GRAB under cases (49.66% of all entries), two ranked list
  loops. General higher-order callees remain unresolved: 34,125 unique call
  sites. The census does not miscount partial-closure returns as saturated
  function proofs or CFG back edges as dynamic tail-recursive loops.
- Hole and discipline checks passed. Full compiler shard measurement is
  incomplete: six shards have sequential build/audit/resource records in
  `results/bprime_all_build.json`. A batching prototype did not invoke its
  timing wrapper and was discarded; no fabricated timings were recorded.

Next, after the separate discovery round: adopt its C4 abstraction, finish
all 202 shard measurements using `check_bc_all.py --measure --resume`, rerun
all generator and axiom gates, and land the proof changes with
`scripts/integrate.sh`. PHASES Round 2 remains open in the draft.

Recovery snapshot: git stash `f94e122806aa291761f8f0560015f789ab85426d`
(`bprime Round 2 draft stopped by C4 abstraction gate; preserve for discovery`).
The draft will be restored in this worktree after the log-only integration;
the snapshot is retained as a recovery copy.
