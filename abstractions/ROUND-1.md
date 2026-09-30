# Abstraction discovery, round 1 (2026-09-30)

Triggered by the gate (`scripts/check_abstraction_gate.py`, check_all stage
a8) on cluster C1, and by the request to target the moving minor GC (C3) and
the bytecode program logic (C4). No project goals are closed during the
round (rule 1); the only proofs written are the bake-off's.

## 1. Obligation census

Source: `abstractions/clusters.def` → `abstractions/clusters.tsv`
(`scripts/abstraction_census.py`: cost = proof lines, date = first commit of
the theorem, ship-your-interpreter's history for copied files).

| cluster | shape (what is re-proved, over what) | members | per-case cost | trend | representatives |
|---|---|---|---|---|---|
| C1 run-algebra | determinism, snoc/append/prefix, halting unique, halting excludes divergence, halts-or-diverges, conversions between closures — once per step relation (machine `Step`, `StepsN`/`Steps`; Iris `ReachesN`/`Reaches`; `BcSem` `StepsN`) | 31 | 8.6 lines | **flat** (first quarter 8.6, last 8.6) → gate fired | `Vsa.Machine.Halts.deterministic` (8), `OCaml.Bytecode.BcHalts.det` (18) |
| C2 checker-soundness | an executable runner/checker is sound/complete for its relation | 7 | 4–20 | too few (< 8) | `runTo_sound` (16), `checkFrom_sound` (20) |
| C3 moving-GC representation | each representation component survives a relocation of live blocks | 0 proved; ≈ 40 upcoming (value words, 8 object kinds, stack, heap disjointness, channels, 15 loop-head fields) | — | target (user) | — |
| C4 bytecode specifications (Layer B′) | specs of bytecode segments/loops | 0 proved; `boot/ocamlc` is 412,087 instructions | — | target (user) | — |

## 2. Laws (checked before the fan-out)

| law | statement | check | result |
|---|---|---|---|
| L1 (C1) | the n-step relation of a deterministic step function is the graph of its fuel-bounded iterate; every C1 fact is a corollary | `round1/check_laws.py`: 20,000 random finite systems, the relational closure vs the iterate, prefix, halting uniqueness, halting excludes divergence, trichotomy | 0 counterexamples |
| L3 (C3) | every representation predicate is invariant under relocating each live block as a whole to a new range, target ranges pairwise disjoint, pointer words rewritten through the relocation, other words copied | `round1/check_laws.py`: 20,000 random heaps | 0 counterexamples; **with overlapping targets 12,358 counterexamples** — disjointness of the targets is part of the law, injectivity of start addresses is not enough |
| L4 (C4) | a bytecode step is local: it reads a bounded footprint and leaves the rest unchanged | `round1/CheckL4.lean`: along real runs (`while`, `while_min`, `f2_closures`), perturb a stack slot deeper than the instruction reads, compare the two steps | 0 violations in 78,855 perturbed steps (stack locality; heap locality not exercised) |

## 3. Held-out pilot suite

`abstractions/pilot/Pilot.lean` (typechecks; the two programs run as
intended by kernel evaluation). Nobody has proved any of these:

* C1: **H1** halting is unique for any `VsaIris.MachineModel`; **H2**
  `Reaches ↔ ∃ n, ReachesN`; **H3** a `Good` program diverges iff it does not
  halt; **H4** a never-stuck machine diverges iff it does not halt.
* C3: **H5** relocation moves exactly the heap pointers (`valWord`); **H6** an
  object's layout (`ObjAt`) survives relocation; **H7** the stack region
  (`StackRepr`) survives relocation.
* C4: **H8** a straight-line segment from any state (symbolic stack);
  **H9** a counting loop from any start `i ≤ 10`.
* Refactors: **R1** the `BcSem` run-determinism block
  (`OCaml/Bytecode/Semantics.lean`: `StepsN.det`, `snoc`, `stop`, `prefix`,
  `halts_or_diverges`, `BcHalts.not_diverges`, `BcHalts.det`; 76 lines);
  **R2** the machine run-composition lemmas (`OCaml/Refinement.lean`:
  `StepsN.append`, `Steps.trans'`, `Halts.of_steps`, `StepsN.prefix'`; 22
  lines); **R3** `OCaml/Logic/BcModel.lean`: `reaches_stepsN`,
  `halts_bcHalts` (21 lines).

## 4. Retrieval by law

Searched by the laws' phrasing, not the project's.

* L1 → **known.** Generic closure libraries: stdpp `relations` (`rtc`,
  `nsteps`, `bsteps`, their lemmas, once for all relations)
  ([coqdoc](https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.relations.html));
  Mathlib `Relation.ReflTransGen`
  ([docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html)).
  Neither states the *deterministic-function* specialisation as one law;
  the project has no Mathlib.
* L3 → **known.** CompCert's memory injections: a partial map from blocks to
  (block, offset), with operations required to commute with it
  ([Leroy et al.](https://arxiv.org/pdf/0902.2137),
  [memory simulations](https://arxiv.org/pdf/2312.08117)). Copying-GC
  verification states correctness as an isomorphism of reachable subgraphs
  (Wang, Stark, Appel, *Verification of a Generational Garbage Collector*,
  Rocq/VST, OCaml-compatible, 2026, [arXiv 2609.13186](https://arxiv.org/abs/2609.13186);
  the `gc_graph_iso` predicate); a mark-and-sweep OCaml GC is verified in F*
  (Shamsu et al., [JAR 2025](https://kcsrk.info/papers/verifiedgc_feb_25.pdf)).
* L4 → **known.** Local reasoning / the frame rule of separation logic;
  bytecode program logics whose frame rule is implicit in the call rule
  (proof-transforming compilation to bytecode), and stack-typed separation
  logics for WebAssembly ([Wasm logic](https://arxiv.org/pdf/1811.03479)).

(Round-1/2 candidates and their retrieval status: §5.)
