# Reloc: relocation equivariance by combinators (pilot entrant)

File: `abstractions/pilot/Reloc.lean` (imports `Pilot`, compiled with
`lake env lean -o .lake/build/lib/lean/Pilot.olean abstractions/pilot/Pilot.lean`;
the worktree also needed the three `riscv-lean/*/.lake` build dirs copied
from the main checkout, because `.lake` alone does not carry `LeanRiscv`).
Zero sorry. Axioms: h5 and `ScanCoherent.act` use {propext, Quot.sound};
h6, h7, `heapRepr_reloc` and `globals_reloc` use {propext, Classical.choice, Quot.sound}.

## The abstraction (section 1, SETUP)

* `relocWord μ pl v w` is the typed action on words. A pointer into a placed
  block moves block-affinely; every other word is fixed.
* ATOM LEMMA `valWord_reloc`: `valWord pl v = some w → valWord (reloc μ pl) v = some (relocWord μ pl v w)`.
  `relocWord_fix` and `relocWord_of_post` are its two corollaries.
* `structure Eqv` has named fields `P` (the pre-state, at base `b`), `Img`
  ("`c'` is the μ-image of `c` on the footprint, moved from `b` to `b'`") and
  `transport : P pl b c → Img → P (reloc μ pl) b' c'`.
* Closure combinators: `pure` (a fact about the base), `plFact` (a fact
  about the placement), `and`, `all`, `guard`, `ex` (over non-address data),
  `placed l` (∃ over an ADDRESS bound by `pl.φ l`, which moves to `μ a`) and
  `list` (list-indexed families).
* Atoms: `val` (value points-to; its image is `relocWord`), and `rawW`,
  `rawW32` and `rawB` (verbatim copies).
* Lifted atom `list_val_img`: a value family's image follows from post-form
  hypotheses (`valWord (reloc μ pl) v = some (word c' …)`).
* Footprint windows `CopyIn E n`: a value-free assertion inside `[b, b+n)` is
  imaged by a byte copy of the window. The closure lemmas are
  `and_copyIn`/`list_copyIn`, and the atom lemmas are
  `rawW_copyIn`/`rawW32_copyIn`/`rawB_copyIn`, which rest on `bytesT_congr`.
* `ScanCoherent gcAct μ pl visited` is a named-field structure with fields
  `ptr` and `nonPtr`. It is stated as a documented premise, and
  `ScanCoherent.act` proves that `gcAct w = relocWord μ pl v w` on visited
  values. It is not used by H5–H7.

## Table

Lines are non-blank non-comment lines, counted from the statement line to the end of the proof. The first edit was at 05:18:20. The whole file was drafted in one pass, so the wall times overlap.

| item | lines | wall time (first edit → first successful check) | failed checks |
|---|---|---|---|
| setup (abstraction + rules) | 99 (+3 import/namespace/open) | 05:18:20 → 05:21:31, 3m11s | 1 (`bytesT_congr`: a stray `simp only at this` made no progress) |
| setup: `ScanCoherent` + `.act` (reported separately) | 16 | 05:18:20 → 05:21:02, 2m42s | 0 |
| H5 | 8 | 05:18:20 → 05:21:31, 3m11s | 1 (`simpa` could not infer the word metavariable; fixed by naming `w`) |
| H6 | 59 | 05:18:20 → 05:23:12, 4m52s | 4 (all in the `double` case of `payload_copyIn`: elaborating the `f`/`R`/`n` metavariables against `payload`; fixed with one `show`) |
| H7 | 4 | 05:18:20 → 05:21:02, 2m42s | 0 |
| extra: `HeapRepr` relocation-invariant (`heapEqv`, `heapRepr_iff`, `heapRepr_reloc`) | 25 | 05:18:20 → 05:21:02, 2m42s | 0 |
| extra 2: `VmReprAt.globals` (`globals_reloc`) | 5 | 05:23:12 → 05:24:05, 53s | 0 |

The 59 lines of H6 break down as follows:
* 19 lines transcribe `ObjAt` into combinators (`payload`, `objEqv`, and `objAt_eq`, which is `cases o <;> rfl`).
* 22 lines are `payload_copyIn`, which proves each non-block kind's footprint lies in `[a, a+8·wosize+8)`. This is an arithmetic bound per object kind, built only from closure lemmas.
* 18 lines are glue: the named premise structure `ObjMoved`, `objImg` and `h6`. `objImg` is reused unchanged by the HeapRepr case.

H7 is 4 lines: a 2-line combinator transcription and a 2-line `transport` application. There is no bespoke reasoning. H5 is the atom lemma plus `relocWord_fix`.

There were no refactors in this cluster, so there are no original refactor lines to compare against (R1 76, R2 22 and R3 21 are not targeted).

## What surprised me

* The first design had `ex`'s image as `∀ i, Img i`. That is unsound for use: a pure conjunct inside the ∃ would then have to hold for every witness. The fix is for the image to assume the pre-state for its witness: `Img := ∀ i, P i → Img i`. With that fix, `pure`, `ex` and `placed` compose.
* Moving an address is not "∃ over data". `HeapRepr` needs a separate binder, `placed`, whose image moves the base to `μ a`. Once that binder existed, HeapRepr took 25 lines and passed on its first check. Its disjointness conjunct stays a genuine premise about `μ` (`hsep`, stated on the original addresses). That is the right shape, because it is what the collector must provide.
* `ObjAt` maps onto the combinators definitionally (`cases o <;> rfl`), and so does `StackRepr` (`h7` applies `transport` directly). The only equation that is not definitional is HeapRepr's `∃ a o, …` ordering (`heapRepr_iff`, one `simp only`).
* The only elaboration trouble was unifying a `payload` match arm against an atom lemma whose `f`/`R`/`n` were not yet known. One `show` fixed it. There were no heartbeat or whnf issues.

## Cost of the NEXT component (about 40 remain in `Repr.lean`/`VmReprAt`)

* **A memory cell holding a value at a fixed address** (`globals`, `Caml_state` fields read as values): about 5 lines. `globals_reloc` measured this at 5 lines, 53 s and 0 failures: one `Eqv.val _ (fun _ => sym)` and one `transport`.
* **A raw memory component** (`ChanAt`, `code`, `stackHigh`, `trapsp`, `codeBase`): a transcription of 3–8 lines plus a `CopyIn` window bound of 2–5 lines, by the same closure lemmas. The header/`word32`/byte atoms already exist.
* **Register fields** (`accu`, `env`, `pc`, `spReg`, `extra`): these need ONE new atom, `valReg r`, whose image is `gpr c' r = (gpr c r).map (relocWord μ pl v)`. That is about 6 setup lines once, then 2 lines per field. `pcOf` and `WorldRepr.output` need one more non-memory atom ("unchanged by the move"), again about 3 lines.
* **All of `VmReprAt`**: it is a named-field structure, not a combinator term. One destructuring and reassembly lemma of about 15 lines would glue the field transports together.

Estimate: about 40 lines of new setup (2 atoms plus the VmReprAt glue), then 2–8 lines per remaining component.

## Bridge to the real GC (`ScanCoherent`) and its cost

This premise is not needed for H5–H7, which quantify over the typed `μ`. Discharging it against the real `caml_oldify_one` breaks into three parts:
* **`ptr`**: follows from the Layer A minor-GC simulation's forwarding invariant (forwarded header = 0, field 0 = new address; old blocks have `μ a = a`). Infix pointers (`k > 0`, `Infix_tag`) need a separate line.
* **`nonPtr`** for `int`: bit 0 set (one `decide`).
* **`nonPtr`** for `code`/`atom`: each needs an address-range lemma that the value lies outside `[young_start, young_end)` (from `Layout` plus the malloc'd code/minor-heap disjointness).
* **`nonPtr`** for `raw`: this is the genuine open obligation. `BcSem` must guarantee that a `raw` word on a scanned root is never young-pointer-shaped, or `raw` values must be kept off the scanned roots.

Estimate: about 30 lines for the range facts. The real cost is inside the minor-GC simulation, not here.
