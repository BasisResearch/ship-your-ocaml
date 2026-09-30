# Round-1 bake-off: the INCUMBENT entrant

The held-out suite (`Pilot.lean`, H1–H9) proved in the project's current
vocabulary and proof style, with no new general abstraction:
`abstractions/pilot/Incumbent.lean`. Checked with
`lake env lean abstractions/pilot/Incumbent.lean` (Pilot compiled to
`.lake/build/lib/lean/Pilot.olean`), under `systemd-run --user --scope -p
MemoryMax=30G`. No `sorry`/axiom/`native_decide`, no heartbeat raise.

Lines count the non-blank, non-comment lines from the `theorem` to the end of
the proof, including case-specific helpers. Minutes are wall-clock minutes to
the first successful check. A failed attempt is a failed check of
`Incumbent.lean`.

## Setup cost

0 (the incumbent has no abstraction to build).

## Held-out cases

| case | lines | minutes | failed attempts | notes |
|---|---|---|---|---|
| H1 | 16 | 2.3 | 2 | helper `h1_aux` (13): induction on the first `Reaches`, then case on the second. The Iris layer has no determinism lemma, so this re-proves `Vsa.Machine.Halts.deterministic` for `MachineModel` |
| H2 | 9 | < 1 | 0 | one direction by induction; the other is the existing `ReachesN.reaches` |
| H3 | 9 | 0.5 | 0 | corollary of the existing `halts_or_diverges` and `BcHalts.not_diverges` |
| H4 | 13 | < 1 | 0 | `Diverges.not_halts`, then induction on the fuel using `StepsN.toSteps` and `StepsN.append` |
| H5 | 7 | ~1 | 0 | `simp` on `valWord`/`reloc` |
| H6 | 93 | 2.4 | 1 | helpers `getD_of_bytesT1` (7), `bytesT_congr` (14), `read_of_copy` (8); `h6` (64) cases on the 8 object kinds. Six of those kinds repeat the same read-of-copy shape |
| H7 | 3 | < 1 | 0 | `StackRepr` is (region, per-slot `valWord`), and the premise of H7 is the second component |
| H8 | 11 | < 1 | 0 | four hand-written intermediate states, `rfl` per step |
| H9 | 62 | 8.6 | 2 | helpers `runN` (5), `runN_sound` (10), `stepsN_append` (5), `loopAt` (3), `inc` (1), `inc_eq` (4), `loop_iter` (9), `loop_exit` (5), `loop_from` (15); `h9` (5). Failure 1: `rfl` over a whole 63-step run hit the 200000-heartbeat `whnf` timeout, and the budget was not raised. Failure 2: a 6-step `rfl` with the post-state written as `ofNat (n+1)` fails, because the elaborator cannot evaluate `untag (tag64 …)` definitionally. The fix states `OFFSETINT` as `step` computes it, then rewrites with a per-`n` `decide`. Two diagnostic probes in a scratch file are not counted as attempts |
| **total** | **223** | **≈ 19** | **5** | |

## Extra measurements (coordinator's requests)

These use the same rules as above. The statements for (a) and (b) are the
rival's (`heapRepr_reloc`, `globals_reloc` in the relocation entrant's
`abstractions/pilot/Reloc.lean`). The `ObjMoved` premises are inlined as in
H6, and the rival's `relocWord` definition is copied as statement vocabulary.
When I read those statements, the printed range also showed the rival's proofs
of `h6`, `h7`, `heapRepr_reloc` and `globals_reloc`. Those proofs use the
rival's `Eqv` machinery, which is not available here, and none of it was used.

| case | lines | minutes | failed attempts | notes |
|---|---|---|---|---|
| (a) `heapRepr_reloc` | 29 | 3.0 (a+b together) | 0 | 21 lines for the theorem. The other 8 come from refactoring H6's body into `objAt_reloc`, which drops H6's unused `8 ≤ μ a` premise (the rival's hypotheses do not include it); `h6` now calls `objAt_reloc`. The proof reuses H6 per live block, and disjointness passes through `reloc`'s `Option.map` |
| (b) `globals_reloc` | 17 | (with a) | 0 | `relocWord` (5, statement vocabulary) + 12: case on the value, `simp` |
| H9_1000 | 41 | 3.4 | 0 | Reuses H9's `runN`, `runN_sound`, `stepsN_append` and `loopAt`. New: `bleint1000_false` (3) and `inc1000` (3), both `decide +kernel` over all `n < 1000`; `bleint1000_step` (7), the one symbolic step; `loop1000_iter` (7), symbolic in `n`; `loop1000_from` (16); `h9_1000` (5). The statement (`loopP1000`, `H9_1000`) is copied and not counted. H9's per-value case split (10 `rfl`s) would not scale, so the iteration is made symbolic and only the two bit-vector facts are decided per value. Two scratch probes failed and are not counted: `bv_omega` proves neither fact, because it does not handle `signExtend`/`sshiftRight`. The whole file checks in about 2 minutes, the same as before, so the kernel `decide` over 1000 values is cheap. At 2^62 values that `decide` would not scale; this route needs a bit-vector lemma for the tagged increment beyond about 10^5–10^6 values |

## Refactors (the incumbent's numbers are the existing sizes)

| refactor | lines |
|---|---|
| R1 `BcSem` run-determinism block (`OCaml/Bytecode/Semantics.lean`) | 76 |
| R2 machine run-composition lemmas (`OCaml/Refinement.lean`) | 22 |
| R3 `OCaml/Logic/BcModel.lean` conversions | 21 |
| **total** | **119** |

## Observations

* C1 (H1–H4, 47 lines) is cheap wherever the relation already has its
  run-algebra lemmas (H2–H4). It is paid in full wherever it does not (H1:
  determinism re-proved for the Iris layer). H9 had to re-prove `StepsN.append`
  for `BcSem`, which the machine already has (R2).
* C3 (H5–H7, 103 lines) is dominated by H6. The byte-copy cases of the object
  kinds repeat the same shape, each with its own `show` of the read width. The
  relocation argument itself is trivial.
* C4 (H8–H9, 73 lines): straight-line code is cheap if the author writes out
  the intermediate states. A loop needs a hand-written fuel runner, its
  soundness proof, a loop-head predicate and a per-value iteration lemma. The
  run cannot be evaluated symbolically in one `rfl` within the budget, and
  the 63-bit tagged arithmetic has to be split out and decided per value.

## `#print axioms`

```
h1: does not depend on any axioms
h2: does not depend on any axioms
h3: [propext, Classical.choice, Quot.sound]
h4: [propext, Classical.choice, Quot.sound]
h5: [propext, Quot.sound]
h6: [propext, Classical.choice, Quot.sound]
h7: [propext, Classical.choice, Quot.sound]
h8: [propext, Classical.choice, Quot.sound]
h9: [propext, Classical.choice, Quot.sound]
heapRepr_reloc: [propext, Classical.choice, Quot.sound]
globals_reloc: [propext, Classical.choice, Quot.sound]
h9_1000: [propext, Classical.choice, Quot.sound]
```
