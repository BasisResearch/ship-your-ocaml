# Lane a1-arms

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

## Open / next

Continue with remaining arithmetic, heap mutation/allocation and control
families: represented SWITCH selection and target adapters are next; OFFSETREF can reuse the proved
operand-width arithmetic. MULINT consumes the proved libgcc summary, and
CHECK_SIGNALS consumes the concrete runtime no-pending invariant.
All six C_CALL opcodes have generated machine boundaries, represented
setup/return bridges and named callee composition. There are 105 conditional
represented opcode bridges (C_CALLs cover returning `.ok` primitives),
not an unconditional `ArmSim.next`. Entry and halt remain open. `whileMin_bcSem`
is bytecode-level; no machine `whileMin` theorem is claimed.

The full captured boot `Loaded` witness has landed (`bc63ae6`) and consumes
the strengthened platform, primitive and atom-table bindings. The arm adapters
still need to derive dispatch clock/geometry and operand/heap access conditions
from an invariant preserved by every family. Runtime preservation remains
explicit. The OFFSETINT/OFFSETREF width correction has landed; its old obstruction
stays as a regression witness. Negative-ATOM and pointer-branch domain gaps
remain recorded above. The approved `GcSafe P` premise is now in
ArmSim and the headline; concrete GC-boundary and whileMin safety proofs
remain to be supplied. Primitives
remain a1-prims' responsibility; C_CALL bodies must consume their named machine
summaries. Allocation slow paths and relocation are a6-gc's responsibility.
