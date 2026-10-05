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
`code : DispatchCode P s c op` is the named obligation for a2-sem's
`CodeFacts.lean`: opcode-word geometry, fetch, not a method-cache slot.
Model row: `acc0_next` (`AccRows.lean`).
