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

## `whileMin_halts_f1`: the premises still open (a1-arms audit, 2026-10-20)
`whileMin_halts_open (o : WhileMinOpen)` (generated `Sim/WhileMinTable.lean`)
is `whileMin_halts_f1 heap growth pre`. Its only premises are
`WhileMinOpen`'s four fields. Every other input is a theorem whose axioms are
⊆ {propext, Classical.choice, Quot.sound}. whileMin reaches 50 opcodes
(`whileMinOps`, one shape run). Among them, SETGLOBAL is the only barrier row,
and C_CALL1/2/4 are the only call rows. C_CALL3 and C_CALL5 are vacuous
(`absurd h (by decide)`).

| premise (where it enters) | status | owner | discharged by / waiting on |
|---|---|---|---|
| `heap`: `cut_heapReady_covers_Statement f1Covered [(refTable, 56)]` (`WhileMinOpen.libHeap`) | **open** | a0-boot | the reset run reaching the cut; caml_init_gc reached end to end (`9ba5a6b9`) |
| `growth.paths.empty`: the unallocated table's growth (SETGLOBAL's barrier) | **proved** | a2-sem / a6-gc | `f1_barrierGrowth (growthCallState _)` (`6305f769`) over `f1_barrierGrowth_gprs` (`076fd054`) |
| `growth.full`: `BarrierGrowthFull Gc.f1Layout` (`F1GrowthPremises.full`) | **open**, by decision (2026-10-13) | a6-gc (G2) | G2's `CollectionEffect`. As stated it is not provable under G1, because the overflow requests a minor GC (a6-gc log, "Obstruction") |
| SETGLOBAL barrier row: `f1_globalBarrier f1_barrierRuntime …` | **proved** | a1-arms / a6-gc | `8811ba3f` |
| `c_call1_returns`: `caml_fresh_oo_id` | **proved** | a1-prims | `prim_caml_fresh_oo_id_returns` (`03604487`) |
| `c_call1_returns`: `caml_ml_open_descriptor_out` | **proved given `OpenOutRuntime Gc.f1Layout`** | bprime (summary) | `prim_caml_ml_open_descriptor_out_returns` (`4d98b8b3`) |
| `OpenOutRuntime Gc.f1Layout` (`WhileMinOpen.openOutRuntime`): `custom`, `after` | **open** | a6-gc | `CustomMemCall` for `f1Layout` (the quiet path of `caml_alloc_custom_mem`) |
| `OpenOutRuntime Gc.f1Layout`: `pins` | **free** | — | `fun c ok => ok.freeListShape` (`f1Layout.runtimeOk` is `RuntimeOk F1Pins`) |
| `OpenOutRuntime Gc.f1Layout`: `budget : ∀ c, runtimeOk c → ∃ k, Ready (k + 1) c` | **open, no owner; not derivable from `runtimeOk`** | **a1-arms (taken 2026-10-20)** | see below |
| `c_call1_returns`: `caml_ml_string_length` | **proved** | a1-prims | `prim_caml_ml_string_length_returns` (`53a7adea`) |
| `c_call1_returns`: `caml_ml_flush` | **proved** | a1-prims | `prim_caml_ml_flush_returns` (`41c1c810`) |
| `c_call2_returns`: `caml_format_int` (`WhileMinOpen.format_int_c_call2`) | **open** | bprime (started 2026-10-20) | `prim_caml_format_int_returns` |
| `c_call2_returns`: `caml_ml_output_char` | **proved** | a1-prims | `prim_caml_ml_output_char_returns` (`41c1c810`) |
| `c_call4_returns`: `caml_ml_output` | **proved** | a1-prims | `prim_caml_ml_output_returns` (`61c3b012`) |
| per-site assembly (`whileMin_ccallReturns`, `whileMinCalls`) | **proved** | a1-arms | `9aa10143` |

Outside whileMin, the general headline `ocamlrun_refinement_F1_open`
(`Sim/F1Ccall.lean`) adds `F1CcallOpen`'s fields:
* `caml_register_named_value` (a1-prims) and `caml_format_int` (bprime) at
  every arity;
* the arity-fixed console and fresh-id summaries at the larger `C_CALLk`;
* `OutListRuntimeL` (a6-gc / a0-boot). Its `entry` has the same budget gap
  (`Ready (k + listed)`).

### The custom-allocation budget (a1-arms)
* **Why it is not derivable.** `budget` quantifies over every
  `f1Layout.runtimeOk` config. Neither `F1Pins` nor `RuntimeOk` constrains
  `caml_extra_heap_resources`, and its doc says the premise is "False after
  the fifth since the cut". The 6th custom allocation requests a major slice
  (Kiran's decision of 2026-10-13: `Ready` carries fewer than 5 prior
  allocations, and the major-slice path is a named open premise). The
  argument is not yet machine-checked: a `runtimeOk` config with the
  counter past the quiet range is not constructed in Lean.
* **Consequence.** `WhileMinOpen.openOutRuntime` cannot be discharged, even
  though whileMin stays on the quiet path.
* **Plan.**
  1. Count custom allocations since the cut where they can be read at a C_CALL
     entry: the represented world's opens and listings, tied to
     `caml_extra_heap_resources` by the runtime invariant.
  2. Put the G1 bound in scope as a BcSem guard on the allocating primitives,
     like the 64-channel guard (`b601b2fe`); a2-sem owns `stepI`.
  3. Restate `budget` (and `OutListRuntime.entry`'s `Ready`) at the C_CALL
     entry whose primitive succeeds, so it follows from the guard.
* **Decided (a2-sem, a6-gc, bprime, 2026-10-20).** Count per channel, as io.c
  does (`caml_alloc_channel`: `chan->refcount++`).
  - **Landed in this batch:**
    - `Chan.refs`: `openChan` sets 1, `caml_ml_out_channels_list` adds 1 per
      listed channel (`listRefs`), close leaves it.
    - `World.customs` (Σ refs).
    - The bound `Budget.customs` in `Fits` (`FitsAt`), with
      `g1Budget.customs = quietBound = 5`. It is not a BcSem guard: the
      compiler differential runs ocamlc on BcSem with more than 5 custom
      allocations. whileMin is within 5, by its shape run.
    - `Gc.RefcountSum` over the open-channel list (0 at the cut:
      `RefcountSum.of_null`).
    - `Fragment.customLedger` and the difftest `f1_chanrefs`.
  - **Next:**
    1. a6-gc: the concrete `Customs` and `F1Pins.customs : Customs c n` at
       `RefcountSum c.σ.mem n`, plus the step across a call.
    2. a1-arms: `ChanAt`'s refcount word `= ch.refs`.
    3. a1-arms: `budget` restated at the succeeding C_CALL entry, with
       `Ready := ReadyOf Customs`. bprime sees the diff first.
