# EffTree: bake-off measurements

This entrant presents each instruction as a first-order effect tree `Eff` over VM-state operations: `getPc`/`setPc`, `getAccu`/`setAccu`, `peek`/`poke`/`push`/`pop`, `halt`, `wrong` and `unsupported`. The tree lives in `Type 0`, and its continuations are ordinary functions.

The file `abstractions/pilot/EffTree.lean` contains:
- one interpreter, `interp`;
- one locality theorem, `interp_frame`, proved by induction on `Eff`. If the stack footprint `Eff.Local d` stays within the top `d` slots, running on `top ++ rest` gives the same result as running on `top`, with `rest` appended.
- a lift of that theorem to runs, `LRun.frame`;
- one rank loop rule, `LRun.loop`.

`Semantics.lean` is unchanged. A `Bridged i need` fact links each opcode to its tree. The fact has two named fields: `step : stepI P s i = interp (effOf i) s`, and `foot`, the stack footprint.

Targets are H8 and H9, plus a scaling probe, H9_1000. The probe is self-stated, uses `BLEINT 1000`, and is not part of the decision. Pilot is imported via `import Pilot` after `lake env lean -o .lake/build/lib/lean/Pilot.olean abstractions/pilot/Pilot.lean`. That compile needed the `riscv-lean/*/.lake` builds copied from main as well as `.lake`. The whole file checks in 5.6 s.

Axioms: `h8`, `h9`, `h9_1000` and `br_*` each use only [propext, Classical.choice, Quot.sound]. The file contains no `sorry`, `native_decide`, `bv_decide` or heartbeat change.

## Table

Line counts are non-blank, non-comment lines. Wall time runs from the first edit to the first clean check, from `date`. Failed checks count every `lake env lean` run that reported an error for that item.

| item | proof lines | wall time | failed checks |
|---|---|---|---|
| **setup** total | **163** | 6 min (05:21:36→05:27:38) | 6 |
|   `Eff`, `interp`, `Eff.Local`, frame, `interp_frame` (by induction on `Eff`) | 80 | | 3 |
|   `Bridged`, `LRun`, `.append`, `.frame`, `.loop` (rank rule) | 35 | | (in the 3 above) |
|   `effOf` arms for the 10 opcodes + `effAdv`/`effJump` | 26 (arms alone: 20) | | 0 |
|   `bridge` tactic (one macro for all opcodes) | 7 | | 3 |
|   `br_*`: one line per opcode, 10 opcodes | 10 | | (in the 3 above) |
|   `lstep` step macros | 5 | | 0 |
| **H8** | **11** | 4.4 min (05:28:41→05:33:05) | 4 |
| **H9** total | **73** | ≈19.5 min (arith 05:16:40→05:21; loop 05:33:30→05:48:27) | 9 |
|   tagged-int arithmetic (`OFFSETINT 1`, `BLEINT B` on `ofNat i`) | 25 | ≈4.5 min | 4 |
|   `LoopCode`, `LoopAt`, `loop_spec`, `loopRun` (generic in the bound `B`) | 45 | | 5 |
|   `h9` itself (7 decode `decide`s + instantiation) | 3 | | 0 |
| **H9_1000** (scaling probe) | **3** proof lines (+8 to state `loopP1000`/`H9_1000`) | <1 min marginal | 0 |
| Refactors R1–R3 | not targeted | — | — |

Setup is 163 lines. Of these, 30 are per-opcode: the 20 `effOf` arm lines and the 10 `br_*` lines. The other 133 are generic.

## Per-opcode cost of the bridge

The table gives, per opcode, the `effOf` arm lines plus the `br_*` line. The shared `bridge` tactic proves every `br_*`.

| opcode | effOf arm | br |
|---|---|---|
| ACC0, PUSH, CONST2, CONSTINT, ASSIGN, BRANCH, STOP | 1 each | 1 each |
| ADDINT, BLEINT | 4 each | 1 each |
| OFFSETINT | 3 | 1 |

The average is 2.0 arm lines plus 1 bridge line, about 3 lines per opcode. All 10 bridges went through the single `bridge` macro: `rcases` the state, unfold `stepI`/`effOf`/`interp`, then `repeat' (split | rfl | subst_vars; simp_all)`. The footprint half is proved by the same macro.

## Estimated cost for all ~150 opcodes

`stepI` has 273 lines and 120 arm lines. `stepI` is used only by `step`: `grep` finds it in `Semantics.lean` only.

**Route A: bridge per opcode, `Semantics.lean` unchanged.**
- Transcribing each arm into `effOf` costs about 1.8–2 lines, the same size as `stepI`'s arm. Each `br_*` line costs 1 more. Over ~150 opcodes that is about 150 × 3 ≈ **450 lines**.
- The vocabulary must grow to cover env, `extra`, `trap`, the heap (`getField`/`setField`/`alloc`), the world/primitive call, and a whole-stack read for `raiseTo`, `APPTERM` and `RESTART`. That is about 8 constructors at roughly 15 lines each across `Eff`, `interp`, `Local` and `interp_frame`, so about **120 lines**.
- Heap locality needs a second frame theorem over a heap footprint, at least 60 lines.
- Total: about **600–650 lines**. The risk is that the uniform `bridge` tactic does not close the `SWITCH`, `CLOSUREREC` and `C_CALL`/`primF1` arms, each of which would need a hand bridge.

**Route B: redefine `stepI i := interp (effOf i)`.**
- The 273-line `stepI` is replaced by `effOf` arms of about the same size, so the net is about **0 lines**.
- The `br_*` lemmas disappear: `Bridged.step` becomes `rfl`, and only `foot` remains. `foot` is automatic from the same macro, so it could be one generic `decide`-free lemma per opcode or a generated table.
- The vocabulary extension is the same as in route A, about 120 lines, plus the heap frame of about 60 lines.
- The only downstream consumer is `step`. The `decide +kernel` runs on `runTo` would then evaluate through `interp`, which is untested.
- Total: about **180–200 new lines** plus a rewrite of `stepI` that changes no statement.

Route B is cheaper by about 400 lines and removes a proof obligation per opcode.

## What surprised me

- `interp_frame`, the one locality theorem by induction on `Eff`, went through on its first check once the names were fixed, in 36 lines. `LRun.frame` lifts it to `BcSem` runs in 8 lines.
- One 7-line tactic proved all 10 bridges, including the stack footprint.
- The real cost of H9 was **tagged-integer arithmetic**: `untag (tag64 (ofNat i) + (1 <<< 1)) = ofNat (i+1)`, and `BLEINT` via `sle` = `decide (B ≤ i)`. That took 25 lines and 4 failed checks, and `Eff` does nothing for it. Any bytecode logic will need this lemma battery once, for tagged `+`, `OFFSETINT` and the `B*INT` branches.
- "From any state" for the non-stack registers, which are env, heap, world and so on, is not a proved naturality lemma. It comes from `interp` computing by `rfl` on an `rcases`'d symbolic state. Only the stack needs the frame theorem.
- Pitfalls that cost failed checks, none of them caused by the abstraction:
  - reusing the named metavariable `?t` in a second `refine` gave an `isDefEq` heartbeat timeout;
  - a `structure … : Prop` cannot carry the `Nat` counter, so it became `∃ i, LoopAt B r i s`;
  - `decide` rejects goals with free variables, so the step macro runs `dsimp only` before `decide`.

## Cost of the next case in the cluster

- **A new opcode:** one `effOf` arm plus one `br_X … := by bridge` line, about 2–5 lines, as long as it uses only the existing operations. Otherwise extend `Eff`, `interp`, `Local` and one `interp_frame` case, about 15 lines, once per new operation.
- **A new straight-line segment**, like H8: about 8–11 lines. Each instruction is one `lstep br_X`, and the frame onto an arbitrary stack is one `LRun.frame` line.
- **A new counting loop with a different bound:** 3 lines. H9_1000 is `loopRun` plus 7 decode `decide`s, because the proof is generic in `B`.
- **A structurally new loop:** about 40 lines. You need its own decode structure, its invariant structure, and one `LRun.loop` instantiation with one `lstep` per body instruction. The rank rule itself is reused.
- **A loop or segment touching the heap:** blocked on the missing heap operations and heap frame, about 80 lines of setup once.
