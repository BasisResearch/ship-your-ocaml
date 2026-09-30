# Membrane: pilot bake-off measurements (H8, H9)

Entrant `Membrane` (`abstractions/pilot/Membrane.lean`) combines two parts:

* **Symbolic stepping.** The real `OCaml.Bytecode.step` is reduced on a
  template state `⟨pc, a, stk, e, x, t, h, w⟩` whose other fields are free
  variables. A straight-line segment is one equation
  `runN P k tpl = some tpl'` closed by `rfl`. There is no per-instruction
  lemma and no second semantics.
* **One loop rule.** `loop_rule` takes a section `Inv`, a rank `μ`, a body
  obligation and an exit obligation, and proves the post from every `Inv`
  state by well-founded induction on `μ`.

Build: `Pilot.lean` compiled to `.lake/build/lib/lean/Pilot.olean` with
`lake env lean -o`, then `import Pilot`. The worktree also needed the
`riscv-lean/*/.lake` build dirs, copied from the main checkout. Axioms of
`h8`, `h9` and `h9_1000` are `[propext, Classical.choice, Quot.sound]`.

## Table

Lines are non-blank, non-comment lines, from the statement to the end of the
proof. Times are wall-clock, from the first edit to the first successful check.

| item | lines | wall time | failed checks |
|---|---|---|---|
| setup (section 1, 15 decls) | 89 | ~7 min (05:16–05:23) | 4 |
| · run algebra: `runN`, `runN_step`, `runN_add`, `runN_seq`, `runN_sound` | 26 | | 0 |
| · branch resolution: `step_br_fall`, `step_br_taken` | 9 | | 0 |
| · `loop_rule` | 14 | | 1 (`Nat.strong_induction_on` does not exist; `Nat.strongRecOn`) |
| · word normalisation: `ofNat_msb`, `longVal_toNat`, `tag64_toNat`, `untag_ofNat`, `offsetInt_ofNat`, `sle_ofNat` | 36 | | 3 (probes: `1` vs `1#64` literal, `toNat_truncate` name, `toInt` case split) |
| · `headNat` | 4 | | 0 |
| **H8** | **9** | ~4 min to route (05:16–05:19:40); passed in file on first check 05:22:56 | 2 |
| **H9** (bound-generic, as committed) | **48** | ~5 min total (see below) | 2 |
| · `loopN`, `arg_natCast`, `bleint_loop` | 10 | | |
| · `loopN_body` (one symbolic body run) | 8 | | 1 |
| · `loopN_exit` | 7 | | |
| · `loopN_reaches` (the loop rule applied) | 22 | | |
| · `h9 := loopN_reaches 10 (by decide)` | 1 | | |
| H9, first (concrete-bound) version: `loop_body` + `h9` | 29 | 05:22:18–05:23:35 | 1 |
| Refactors R1–R3 | not targeted | — | — |

Failures:

* **H8.**
  * `rfl` straight to `accu = .int 42` failed with "not definitionally
    equal".
  * `decide +kernel` failed because a template has free variables.
  * `with_unfolding_all rfl` hit the max recursion depth.
* **H9, first version.** `rw [hb]` did not fire because the goal had
  `(10 : Int)` and `hb` had `((10 : Nat) : Int)`.
* **H9, bound-generic version.** Implicit `n` in `step_br_fall` unified to
  the unreduced `(loopN N).code[…].toInt`. It has to be pinned explicitly.

## Scaling probe: H9 with bound 1000 (not part of the decision)

`H9_1000` is stated in the file with `loopP1000`, which is `BLEINT 1000` and
otherwise the same program. It is proved two ways:

* **Concrete copy.** Replacing 10 by 1000 in the H9 proof gave 32 lines
  (9 for the body and 23 for the main proof). It checked on the first try,
  about 45 s from edit to check, with 0 failures. The cost does not depend on
  the bound: one symbolic body run, and `omega` over `i < 1000`.
* **Bound-generic (committed).** `loopN_reaches N (hN : N < 2^31)` proves the
  loop for every bound, so `h9_1000 := loopN_reaches 1000 (by decide)` is
  **1 line**. It needed 0 extra failures, after 1 failure for the
  generalisation.

The incumbent enumerates the 11 start values, and that grows with the bound.
Here the bound only enters as `omega` arithmetic and as the `decide` of
`N < 2^31`. The kernel never runs the loop.

## Where reduction on symbolic states got stuck, and why

1. **Data-dependent branches (expected).** `brOp`'s `if` on
   `sle (ofInt 64 N) (longVal i)` with symbolic `i` does not reduce.
   `step_br_fall` / `step_br_taken` resolve it: the decode-to-arm equation
   `step P s = brOp s n o f` is `rfl`, and the one Boolean fact comes from
   `sle_ofNat` + `omega`. The same need will appear for every helper that
   branches on a symbolic word (`BRANCHIF`/`BRANCHIFNOT`, `cmpOp`, `EQ`,
   `SWITCH`). That is one rule per helper, written once.
2. **Normalising a closed literal inside a symbolic run.** `rfl` of the
   4-step H8 run against `accu = .int 42` fails. The same run is `rfl`
   against the unnormalised `.int (untag (tag64 2 + tag64 (ofInt 63 40) - 1))`,
   and one `decide` closes the literal. Each part alone is `rfl`, so the
   likely cause is the elaborator's lazy-delta heuristics on the combined
   problem. I did not investigate further, because the split matches Law 1:
   ground literals are checked separately.
3. **Symbolic data in the code array.** With a symbolic bound in the
   program, decode leaves the operand as `(BitVec.ofInt 32 ↑N).toInt`.
   Unification then prefers the unreduced array-index form, so the branch
   operand has to be named explicitly. `arg_natCast` normalises the operand.
4. **Never stuck on the rest of the state.** The stack tail, env, extra,
   trap, heap and world are carried through the `{ s with … }` updates
   untouched.

## Cost of the next case in the cluster

* **New straight-line opcode:** 0 lines if its arm matches only on
  constructors present in the template. `rfl` reduces any such F1 arm.
* **New branching helper:** about 5 lines, once, in the `step_br_*` style.
* **New integer op on symbolic ints:** about 6–9 lines, once. It is one
  `toNat` normalisation lemma, like `offsetInt_ofNat`, closed by `omega`.
* **New loop:** about 30–40 lines, the same shape as H9 (section, rank, body
  run, exit run, rule application).
* **Nested loops:** the inner loop's lemma is a segment inside the outer
  body, joined with `runN_seq`. This is not measured.
* **Segments that allocate and then read:** unverified. `Heap.alloc` on a
  symbolic heap stays a term, so a later `GETFIELD` would need an
  `alloc`/`get?` lemma. This is the likely next place reduction gets stuck.

## Surprises

* Decoding the concrete code (`enc`, `Opcode.ofNat?`'s 149 arms,
  `List.mapM`) under `rfl` was cheap. Each check of the whole file, including
  loading the imports, took about 30–47 s on a shared machine.
* Generalising H9 over the bound cost about 20 lines and made every other
  bound free. Keeping two concrete copies would have broken Law 3.
* Protocol deviation: two checks ran with less than 25 GB available (19 GB and 11 GB).
  Both ran under `MemoryMax=12G` and passed.
