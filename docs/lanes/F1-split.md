# F1 ownership split (foreman, 2026-10-05)

The goal is `ArmSim L B P` for F1, then `ocamlrun_refinement_Statement`
(~/Documents/code/syo-lanes/F1.md). Most F1 opcodes already have a
*conditional* bridge `<op>_step_arm` (OCaml/Vm/Sim). What remains:
* derive their premises from the running invariant;
* compose them into unconditional `ArmSim.next` cases.

## The shared running invariant (critical path)
`Running` (the platform/loop-head invariant) must supply every arm's
premises. a2-sem found that four facts are missing.
| fact | owner |
|---|---|
| the machine's tick count is below 2 at the loop head (dispatch clock) | **a1-arms** |
| dispatch registers and stack geometry (stack space, separation) as a preserved invariant | **a1-arms** |
| decode-to-fetch: the decoded instruction at `pcOf c` is the one the ELF image holds (via `Vsa.Sim.ElfDecode` and the image pins) | **a2-sem** |
| a reachable bytecode PC is not an object method-cache slot (F1 never writes code) | **a2-sem** |
| code-address geometry: bytecode PCs map into the loaded code region, in bounds and aligned | **a2-sem** |
| `LibraryReady c` (`OCaml/Vm/Primitives/Memmove.lean`: GPR presence, `gp`, idle HTIF; no RAM presence) at C_CALL entries that call newlib | **a1-arms**: `CcallSetupPost.libraryReady` (`LoopRegisters.gp`); a1-prims carries it through console calls (`GprsKept`, `LibraryReady.of_kept`) |

a2-sem's three facts go in `OCaml/Vm/Sim/CodeFacts.lean`, a new file owned
by a2-sem. a1-arms consumes them and states its own in
`OCaml/Vm/Sim/Invariant.lean`, owned by a1-arms.

## Opcode families → unconditional `ArmSim.next` cases
* **a2-sem**:
  * integer arithmetic and logic: ADDINT SUBINT MULINT DIVINT MODINT ANDINT
    ORINT XORINT LSLINT LSRINT ASRINT NEGINT (`division_step_arm`);
  * comparisons: EQ NEQ LTINT LEINT GTINT GEINT ULTINT UGEINT ISINT;
  * conditional branches: BEQ BNEQ BLTINT BLEINT BGTINT BGEINT BULTINT
    BUGEINT BRANCH BRANCHIF BRANCHIFNOT SWITCH;
  * constants: CONST0–3, CONSTINT, PUSHCONST*, ATOM*, PUSHATOM*;
  * OFFSETINT and OFFSETREF;
  * BOOLNOT.
* **a1-arms**: everything else in F1, namely stack (ACC*, PUSH*, POP,
  ASSIGN), environment (ENVACC*, PUSHENVACC*, OFFSETCLOSURE*), closures
  (CLOSURE, CLOSUREREC), globals (GETGLOBAL*, SETGLOBAL), blocks (MAKEBLOCK*,
  GETFIELD*, SETFIELD*), application and return (PUSH_RETADDR, APPLY*,
  APPTERM*, RETURN, RESTART, GRAB), exceptions (PUSHTRAP, POPTRAP, RAISE*),
  C_CALL1–5 (citing a1-prims' summaries), CHECK_SIGNALS and STOP.
* **bprime**: `ArmSim.entry`, `ArmSim.halt`, and the assembly of `next` from
  the per-opcode cases.

An opcode missing from both lists belongs to a1-arms. Record a disputed or
moved opcode here, in the same commit as the change.

## The arm contract (a1-arms)
`ArmSim` is stated over `LoopAt L P s c` (`OCaml/Refinement.lean`), which is
`Running L P s c` plus `clock : c.tick < 2`. The clock is a run invariant
(`StepsN.tick_lt`): `LoopAt.of_plus h run running` restores it, so no arm
threads it.

`Running` carries `stack : StackPlaced P s c`: a representation witness
together with its `StackGeometry` (`OCaml/Vm/Sim/Invariant.lean`). The VM
stack window `[high - Layout.stackBytes, high)` lies above `.bss`, inside RAM,
and apart from `Caml_state`, the code, every placed object, the channels and
the primitive entries. Every arm bridge proves it for its result at the shared
restore sites. Allocating families take a named `stackApart` premise: the new
object is placed apart from the window (a6-gc's nursery bounds).
`ArmInput.of_loop` enters an arm from `LoopAt` and the code facts
(a2-sem's `CodeFacts.lean`). `InvariantUse.lean` turns the geometry into the
arms' stack premises: `StackGeometry.payload`/`.image`/`.bindings` for any
write in `[high - stackBytes, sp)`, `.read`, `.write`, and `stack_space` from
`Fits` (given `8 * B.stackWords ≤ Layout.stackBytes`). bprime's entry
supplies `StackPlaced` at the cut.

`Running` also carries `native : NativePlaced c` (`∃ D, Invocation D c ∧
NativeValid D`, `OCaml/Vm/Sim/Invocation.lean`), which is preserved by every
arm bridge. `ArmInput.of_loop h code` enters any arm from `LoopAt`.
`code : DispatchCode P s op` is the named obligation for a2-sem's
`CodeFacts.lean`: only the opcode fetch. The F1 code representation is
exact, and the code geometry comes from `StackGeometry.codeLow/codeArena`
(`StackGeometry.code_read`; `OperandAt.of_fetch` for operands).
`StackGeometry` also places the code buffer and the atom table apart from
each other and from every placed object (`heapLow`, `heapCode`, `heapAtoms`;
for word equality). Allocation takes one named `NurseryPlacement` (a6-gc).
Model rows: `acc0_row` (`AccRows.lean`), `push_row`/`pushacc1_row`
(`PushRows.lean`), in `OCaml.OpArm P (OCaml.LoopAt L P) op` form. The shared
row premises are `StackCapacity B` and `RuntimeFrame L high`
(`StackRows.lean`). `PushWriteOk.of_geometry` and `RuntimeFrame.push`
supply every one-word push. `StackGeometry.even : EvenPlace pl` serves
ISINT/BRANCHIF/SWITCH.

## `whileMin_halts_f1`: current ordinary-table premises
`whileMin_halts_open (o : WhileMinOpen)` (generated `Sim/WhileMinTable.lean`)
is `whileMin_halts_f1 growth pre`. Its remaining inputs are
`WhileMinOpen`'s three fields: growth, opening and formatting. Every other input is a theorem whose axioms are
⊆ {propext, Classical.choice, Quot.sound}. whileMin reaches 50 opcodes
(`whileMinOps`, one shape run). Among them, SETGLOBAL is the only barrier row,
and C_CALL1/2/4 are the only call rows. C_CALL3 and C_CALL5 are vacuous
(`absurd h (by decide)`).

| premise (where it enters) | status | owner | discharged by / waiting on |
|---|---|---|---|
| Captured-entry `libHeap` | **proved; removed from WhileMinOpen** | a0-boot | `Gc.whileMin_libHeap` from the captured allocator certificate. Reset-to-cut execution remains separate and open. |
| `growth.paths.empty`: the unallocated table's growth (SETGLOBAL's barrier) | **proved** | a2-sem / a6-gc | `f1_barrierGrowth (growthCallState _)` (`6305f769`) over `f1_barrierGrowth_gprs` (`076fd054`) |
| `growth.full`: `BarrierGrowthFull Gc.f1Layout` (`F1GrowthPremises.full`) | **open**, by decision (2026-10-13) | a6-gc (G2) | G2's `CollectionEffect`. As stated it is not provable under G1, because the overflow requests a minor GC (a6-gc log, "Obstruction") |
| SETGLOBAL barrier row: `f1_globalBarrier f1_barrierRuntime …` | **proved** | a1-arms / a6-gc | `8811ba3f` |
| `c_call1_returns`: `caml_fresh_oo_id` | **proved** | a1-prims | `prim_caml_fresh_oo_id_returns` (`03604487`) |
| `c_call1_returns`: `caml_ml_open_descriptor_out` | **counted interface proved; ordinary row open** | a1-prims / a1-arms | `counted_caml_ml_open_descriptor_out_returns` needs `CountedCcallSetupPost`; ordinary invariant/setup migration remains open |
| `OpenOutRuntime Gc.f1Layout` (counted caller): `custom`, `after` | **open** | a6-gc | `CustomMemCall` for `f1Layout` (the quiet path of `caml_alloc_custom_mem`) |
| `OpenOutRuntime Gc.f1Layout`: `pins` | **free** | — | `fun c ok => ok.freeListShape` (`f1Layout.runtimeOk` is `RuntimeOk F1Pins`) |
| Successful-call readiness | **proved from counted entry + reachable successor + `Fits`** | a1-prims / a1-arms | Universal runtime budget removed; numeric `customBudget` only bounds the layout. Actual ordinary representation producers still need the physical count witness. |
| `c_call1_returns`: `caml_ml_string_length` | **proved** | a1-prims | `prim_caml_ml_string_length_returns` (`53a7adea`) |
| `c_call1_returns`: `caml_ml_flush` | **proved** | a1-prims | `prim_caml_ml_flush_returns` (`41c1c810`) |
| `c_call2_returns`: `caml_format_int` (`WhileMinOpen.format_int_c_call2`) | **open** | bprime (started 2026-10-20) | `prim_caml_format_int_returns` |
| `c_call2_returns`: `caml_ml_output_char` | **proved** | a1-prims | `prim_caml_ml_output_char_returns` (`41c1c810`) |
| `c_call4_returns`: `caml_ml_output` | **proved** | a1-prims | `prim_caml_ml_output_returns` (`61c3b012`) |
| per-site assembly (`whileMin_ccallReturns`, `whileMinCalls`) | **proved** | a1-arms | `9aa10143` |

Outside whileMin, `F1CcallOpen` now lists five ordinary row suppliers:
open-descriptor-out, open-descriptor-in and out-channels-list at `C_CALL1`,
named registration and integer formatting at `C_CALL2`. The counted channel
summaries cannot fill the weaker ordinary rows until their entry producers
carry physical accounting. Wrong arities are still discharged by
`PrimReturnsAtD.of_arity`; the full `GoodF1` domain is unchanged.

The counted route now carries physical/refcount witnesses through loop
placement, entry/setup, shared frames and **132/134 complete opcode rows**.
C_CALL3/5 are complete by the checked arity classification; C_CALL4 has actual
console returns and all rejection cases. Counted fresh-OO-ID success and
native unary exit are also checked. Whole C_CALL1/2 remain open.

`CountedCcall1` and the channel summaries retain actual returned placement,
physical transitions and natural refcount observations. They do not by
themselves produce the allocating primitives' complete runtime invariant.
Listing entry now consumes actual C_CALL setup and stack room;
`OutListF1.f1_outList_entry` derives its selected ledger and spatial facts.
`outList_f1_restore` reconstructs the returned runtime conditional on ordinary
reserve at that same returned capacity. Input credit and native spending must
be propagated on the selected heap to remove that final numeric premise.

### The custom-allocation budget (2026-10-27 continuation)

`Fits` bounds `World.customs` (Σ channel refs) at every reachable state;
`g1Budget.customs = quietBound = 5`. This remains a budget hypothesis, not a
BcSem guard. `openChan_customs` and `listRefs_customs` give the exact semantic
charges, and `CcallSucc.customs_bound` reads the bound at the successful
successor. `open_call_ready` and `out_list_call_ready` combine it with the
represented physical count. The universal `OpenOutRuntimeAt.budget` and the
out-list entry's universal `Ready` field are removed.

`CustomMemCall.call` returns exact count evidence in the actual
`CustomMemCountedReturned` post. The weak `CustomMemReturned` is a projection
for ordinary memory/ABI clients. `CustomAccounting` supplies framing,
uniqueness and `ReadyOf` conversion; it has no universal increment implication
from the weak return. `OpenedOut`, the out-list loop and its final return
retain the exact physical transition. Each listed record charges one custom
allocation, and its cons cell charges zero. `ChannelCustomsAt.pending`
distinguishes the incremented refcount before allocation from the physical
counter.

`CountedVmReprAt`, `CountedCcallSetupPost`, and `CountedResult` name the
stronger boundaries. `f1_channelCounts_of` produces startup channel counts
from the actual empty-list observation and a physical zero witness.
`open_out_counts` produces full physical/refcount representation at the new
placement using the existing shared payload frame.

Still open:

1. Native custom transitions and selected capacity spending remain in the
   accepted named `CustomMemCall` premise. Concrete `PhysicalCustoms`,
   independent read context, startup/caller frames and captured counted entry
   are reviewed in `53e93d16`; reset execution remains separate.
2. Selected custom-allocation credit and returned spending through listing,
   plus the opening call's complete after-runtime reconstruction.
3. Whole C_CALL1 assembly from all unary successes and native exit, and
   C_CALL2's general formatting/named-registration runtime producers.
4. Complete counted F1 assembly, with counted `BarrierGrowthFull` supplied by
   G2. The old ordinary table is not completed merely by weakening away counts.
5. Reset through CODE/PRIM/DATA loading, promotion and system/argv to Loaded;
   captured-memory certificates do not establish that execution.

A blanket implication from every weak `CcallSetupPost` to counted evidence
was removed: source reachability alone does not constrain the omitted
machine counters. This repeats the old universal readiness gap, as recorded
in `DEAD-ENDS.md`. No runtime supplier is claimed closed. Validation commands
and lead-review status are in `a1-prims.md`.
