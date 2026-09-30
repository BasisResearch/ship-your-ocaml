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
| L3′ (C3, round 2) | L3 against the collector's real classifier (a scanned word is rewritten iff even and in the young range) and real traversal (roots, `ref_table`, copied blocks) | `round1/check_laws.py`, 20,000 random heaps each | 0 counterexamples with no young-looking raw words and a complete ref table; **8,664** when a raw word may look young (needs **NoForgery**/scan coherence); **3,123** when an old→young field is missing from the ref table (needs **RememberedComplete**). Two further gaps found in `vendor/ocaml-4.14.4/runtime/minor_gc.c`, not yet in the checker: `caml_oldify_one` short-circuits `Forward_tag` blocks (l. 240–265), and interior pointers are only handled behind `Infix_tag` headers. In `BcSem` the only `Val.raw` written is a `CLOSUREREC` infix header `3072k+249` (odd, `Semantics.lean:533`), so NoForgery costs nothing for raw words |
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


## 5. Candidates (deep seeded fan-out, merged by mechanism)

Two rounds of six blind ontologists each (4 character-string seeds, 2
dictionary-word seeds). Round 1 saw only `round1/BRIEF.md`. Round 2 saw the
brief, the full raw text of round 1, and four facts learnt meanwhile: raw
words, bit-pattern GC classification, no Mathlib, and the `StepResult`
shape. Raw reports: `round1/raw1/r1-*.md` and `round1/raw2/r2-*.md` (R2-3 also
wrote a checked toy, `raw2/r2-3-Toy.lean`).

Agreement:
* 6 of 6 round-1 agents reached a fuel-iterate/orbit kernel for C1, a
  relocation-equivariance fundamental lemma for C3, and a declared-footprint
  (lens/patch/stencil) rule for C4.
* 6 of 6 round-2 agents objected that the C3 relocation was by VM sort while
  the collector classifies by bits. That objection was checked as L3′ (§2).

Tags: R1/R2 = round, c/w = chars/words seed, ↩ = answers or objects to an
earlier idea. Retrieval uses the law's phrasing. **known** carries a
citation; **novel** means no prior formulation was found. Items marked
[check] are recalled, not verified.

### C1 run algebra

* **K1 Fuel-iterate kernel, L1 as the definition.** R1-1#1c, R1-2#1c,
  R1-3#1c, R1-4#1c, R1-5#1w, R1-6#1w.
  * One `iter` with absorbing stops. Shift, absorb, unique, trichotomy and
    closure are proved once.
  * **known:** Capretta's delay monad ([LMCS 2005](https://lmcs.episciences.org/2265)); CompCert `Smallstep` generic star/plus/determinacy lemmas ([coqdoc](https://compcert.org/doc/html/compcert.common.Smallstep.html)); stdpp `nsteps`.
  * The Mathlib-based variants (R1-2, R1-4: `Computation`; R1-4#5: `KleeneAlgebra`) are unavailable here, as R2-2, R2-4, R2-5 and R2-6 objected.
* **K2 Presentation uniqueness.** R2-2#1c ↩K1.
  * `ConsPres`/`SnocPres`/`ClosPres`: constructors plus inversion determine an ℕ-indexed relation. Each legacy relation then enters by a one-line `cases` instead of a ~10-line bridge.
  * **known** in spirit (Lambek's lemma, initial-algebra semantics); **novel** as a proof-engineering interface for step relations, since no library found states it.
* **K3 Timeline decision tactic.** R2-4#1c ↩K1.
  * Its objection: after K1 the residual per-member cost is compositional glue, so it asks for a decision procedure (atom saturation + `omega`).
  * **known** ingredients (Nelson–Oppen combination [check]).
* **K4 Lax, time-changed morphisms.** R2-1A c, R2-6#5 w, R2-3#3 c ↩K1 (a lockstep strict square cannot carry `BcModel`'s lossy `Wrong/Unsupported ↦ stuck`, nor Layer A's 1-to-many steps).
  * `TimeChange` has a positive clock and a lossy outcome map. Backward transport comes from target determinism.
  * **known:** CompCert's forward-to-backward simulation for determinate targets; Kakutani induced maps and stuttering bisimulation [check]. The Layer A reading (ArmSim as `more_sq`) is new to this project.
* **K5 Relation algebra / KAT.** R1-4#5c. **known** ([Kozen, KAT/Hoare](https://dl.acm.org/doi/10.1145/343369.343378)).
* **K6 Oracle skew product for the nondeterministic OS spec.** R2-1D c ↩R1-3#1.
  * **known** (random dynamical systems as skew products; prophecy variables [check]).
* **K7 Certificates and checkers.**
  * Covers the manifest (R1-5#4w), fuel-monotone reflection (R1-3#4c), checkers as `csimp` (R1-6#1w), and a static `Supported` certificate for H3 (R2-3#3c).
  * R2-5 objected to the `csimp` route: `decide +kernel` ignores `implemented_by`.
  * **known** (proof-carrying code, translation validation [check]).
* **K8 Four-valued behaviour oracle + loop ledger.** R1-6#4w. **known** (Belnap FOUR; Floyd ranking [check]).
* **K9 A deterministic `MachWP` instance.** R2-4#5c.
  * Specs stated `∀ Wp` get instantiated at a timeline WP, which yields run facts with no adequacy step.
  * **novel** here; Dijkstra-monad analogue [check].

### C3 moving-GC representation

* **R1 Equivariant representation language.** R1-1#2c, R1-2#2c, R1-3#2c, R1-4#2c, R1-5#2w, R1-6#2w.
  * Predicates are built from combinators whose single atom is the value encoding. A fundamental lemma gives relocation invariance.
  * **known:** nominal equivariance ([Pitts 2013](https://www.cambridge.org/9781107017788)), parametricity, CompCert memory injections.
* **R2 Pullback / naturality / quotient.**
  * Covers `render` naturality (R1-2#5c), `peel` gauge (R1-6#5w), the quotient (R1-5#5w) and gauge-fixed simulation (R1-3#5c).
  * Objected to by R2-6#4w and R2-1E: `Quot` blocks `decide +kernel`, and the relation is not symmetric (young→old only).
  * **known** (CakeML GC partial bijections, [Ericsson–Myreen–Åman Pohjola JAR 2019](https://link.springer.com/article/10.1007/s10817-018-9487-z); heap isomorphism in [Wang–Stark–Appel](https://arxiv.org/abs/2609.13186)).
* **R3 Scan coherence (bit vs sort).** R2-1B c, R2-2#2c, R2-3#1c, R2-4#2c, R2-5#1w, R2-6#1w ↩ all of R1.
  * A named `ScanCoherent`/`NoForgery` field plus one bridge lemma makes any R1/R2 engine a statement about the real collector. **Checked (L3′).**
  * **known** idea (precise GC needs the mutator's tag discipline: type-preserving GC, TAL [check]).
* **R4 Remembered-set completeness.** R2-1E c, R2-2#5c, R2-3#2c, R2-5#3w.
  * The minor collector rewrites only roots, `ref_table` entries and copies. **Checked (L3′).**
  * **known:** CakeML's generational GC treats old pointers as non-pointers.
* **R5 Reachability-closed partial placement.** R2-2#5c, R2-5#2w.
  * Dead blocks leave the placement domain, a step that is Iris weakening.
  * **known** (Morrisett–Felleisen–Harper λgc, FPCA 1995 [check]).
  * `Place.φ` is already partial, so only the "dead leaves the domain" rule is new.
* **R6 The forwarding log is ρ.** R2-4#3c, R2-5#3w.
  * The Cheney loop invariant is expressed in the representation grammar via partial relocations and tricolour.
  * **known** (Cheney; Dijkstra et al.; McCreight et al. [check]).
* **R7 Forward_tag and Infix.** R2-5#3w (confirmed in `minor_gc.c`), R2-3#1c. They require a lax clause for forced lazies and an Infix-only interior-pointer clause.
* **R8 Generational Kripke worlds / one-shot promotion.** R2-1E c. **known** (Kripke logical relations).
* **R9 Lagrangian placement.** R2-6#4w.
  * Placement appears in exactly one `HeapInv`; the GC is a single `wp_localRunW` preserving it.
  * **known** pattern (Iris authoritative heap over physical heap).

### C4 bytecode specifications

* **P1 Declared footprints (lenses/patches/stencils).** R1-1#3c, R1-2#3c, R1-3#3c, R1-4#3c, R1-5#3w.
  * **known:** [Foster et al. TOPLAS 2007](https://dl.acm.org/doi/10.1145/1232420.1232424), [Bancilhon–Spyratos TODS 1981](https://dl.acm.org/doi/pdf/10.1145/319628.319634), [Curtis–Hedlund–Lyndon](https://arxiv.org/abs/1507.02180).
  * Objected to by R2-2, R2-3, R2-4, R2-5 and R2-6: it needs a 150-arm second transcription of `step` (Law 3).
* **P2 Symbolic reduction of the real step (membrane).** R1-6#3w, R1-1#5c, R2-4#4c.
  * **known** (symbolic execution by evaluation).
  * Risk: reduction gets stuck on symbolic heaps (R2-2).
* **P3 Effect-tree step.** R2-2#3c, R2-3#4c, R2-5#4w, R2-6#2w ↩P1.
  * The footprint is the operation log. Locality is proved once by induction on the free monad, with per-operation (not per-opcode) cost.
  * **known:** algebraic effects and interaction trees; optimistic-concurrency read-set validation [check].
* **P4 Loops by sections / ranked circularity.** R1-4#4c (Poincaré), R1-2#4c (reachability logic), R1-6#4w (ledger), R2-5#5w (`tailrec`), R2-1A T5 (Kakutani).
  * **known** ([one-path reachability logic, LICS 2013](https://fsl.cs.illinois.edu/publications/rosu-stefanescu-ciobaca-moore-2013-lics.html); Floyd).
* **P5 Decompilation into Lean by generator.** R2-4#4c, R2-5#5w. **known** (Myreen's decompilation into logic [check]).
* **P6 Code locality and pc-translation equivariance.** R2-1C c, R2-4#4 D2.
  * Specs are proved on 5–50-word slices and lifted, which avoids O(pc) kernel fetches in a 412k array.
  * **novel** as a rule here; linker PIC analogue.
* **P7 Push/enter-aware application summaries.** R2-2#4c (over- and under-application as generic theorems). **known** ingredients (interprocedural summaries; "Making a fast curry" [check]).
* **P8 Emission-scheme grammar.** R2-6#3w.
  * Parse the compiler's output against `bytegen`'s schemes, with one rule per production; the parse tree is the certificate.
  * **known** ingredients (attribute grammars, translation validation).
* **P9 VM resource algebra with per-operation small axioms through the existing Iris WP.** R2-3#5c. **known** (small axioms, Iris ghost state).
* **P10 GKAT.** R1-1#4c.
  * **known.** R2-2 objected: computed transfers dominate ZINC bytecode.

### Chars vs words

| seed type | agents | distinct clusters contributed | clusters only this seed type produced |
|---|---|---|---|
| chars | 8 | 25 | 11 (K2, K3, K5, K6, K9, R8, P6, P7, P9, P10, and K7's static certificate) |
| words | 4 | 18 | 4 (K8, R7's Forward_tag, R9, P8) |

Per agent: chars 1.4 unique clusters, words 1.0. The only confirmed runtime
bug-class that no chars agent found (Forward_tag short-circuiting) came from
a words agent.

### 5.1 Variation (ideonomy, on the top two)

* Draw 1 (abstraction-lift, combination, lattice; polarity, cardinality,
  discovery-vs-invention) on **K1+K4**. It produced a lattice of system
  morphisms: strict ⊑ lockstep ⊑ lax-outcome ⊑ time-change ⊑
  relational time-change. The meet of lax-outcome and time-change is
  Layer A's `ArmSim`. Survivors:
  * **V1 Model-as-class.** "Discovered, not invented": `VsaIris.MachineModel` already is the class, so prove the kernel on it rather than on a new `DetSys`.
  * **V2 Refutation by the same kernel.** Polarity: the kernel should emit `decide`d counterexamples, e.g. an unsupported one-instruction program for the brief's "never-wrong" wording of H3.
* Draw 2 (abstraction-lift, tree-finding, timeline; hierarchicalness,
  homogeneity, autonomy) on **R1+R3**. Survivors:
  * **V3 Relocation records.** Linker sibling: render the VM state together with the list of scanned slots the collector will rewrite. L3 becomes "applying the records commutes with `render`". NoForgery says the records are exactly the young-looking scanned words, and the old-slot records are `ref_table`, so R1, R3 and R4 merge into one object.
  * **V4 Epoch-indexed representation.** The timeline shows placement is static between collections. Only the epoch bump carries obligations, which is R9's shape, reached independently.

The bake-off entrants were chosen as the cheapest-looking candidate per
cluster, plus a rival where the pool split:
* **RunKernel** (K1+K2+K4, V1)
* **Reloc** (R1 with R3 as a stated premise)
* **Membrane** (P2+P4)
* **EffTree** (P3+P4)

## 6. Bake-off

Every entrant was built in its own worktree against `abstractions/pilot/Pilot.lean`
(`abstractions/pilot/<Name>.lean` + `<NAME>.md`). Protocol: the
held-out statements verbatim, zero `sorry`, axioms ⊆ {propext,
Classical.choice, Quot.sound}. All five files were re-checked independently
with `#print axioms` before the decision. Lines are non-blank, non-comment
proof lines. "fails" counts checks that reported an error.

| entrant (cluster) | setup | held-out cases | refactors (orig 76/22/21) | fails | extra cases |
|---|---|---|---|---|---|
| Incumbent (all) | 0 | H1 16 · H2 9 · H3 9 · H4 13 = **47**; H5 7 · H6 93 · H7 3 = **103**; H8 11 · H9 62 = **73** | — (119) | 5 | HeapRepr 29 (21 + 8 helper) · globals 12 (+5 copied def) · H9 at bound 1000: 41, with one kernel `decide` per value below 1000 |
| **RunKernel** (C1) | 240 | H1 2 · H2 2 · H3 6 · H4 12 = **22** | R1 25 · R2 10 · R3 11 = **46** | 2 + 1 + 2 | new `MachineModel`: 0; new step system: ~15–25 lines |
| **Reloc** (C3) | 115 | H5 8 · H6 59 · H7 4 = **71** | — | 1 + 5 | HeapRepr 25 · globals 5; next component 2–8 lines |
| **Membrane** (C4) | 89 | H8 9 · H9 48 = **57** | — | 4 + 4 | H9 at bound 1000: **1 line** (the proof is generic in the bound, so the kernel never runs the loop) |
| EffTree (C4) | 163 | H8 11 · H9 73 = **84** | — | 6 + 13 | H9 at bound 1000: 3; all ~150 opcodes: ~600 lines of bridges, or a ~200-line redefinition of `stepI` |

Wall time (agent-measured, first edit to first clean check):
* incumbent ≈ 19 min for H1–H9;
* RunKernel ≈ 22 min, 12 of them waiting for the memory gate;
* Reloc ≈ 14 min;
* Membrane ≈ 16 min;
* EffTree ≈ 36 min.

Tokens were not measurable per item.

## 7. Decision

The rule: a candidate wins if the held-out cases get cheaper **and** its
refactors shrink.

* **C1: RunKernel adopted.** Held-out 47 → 22 lines (−53%), refactors 119 → 46
  (−61%).
  * Setup (240 lines) is larger than the pilot saving (98 lines). It
    amortises over the remaining run relations: the OS spec, the Layer A
    simulation, and every future model is 0 lines.
  * Landed as `OCaml/Run/Kernel.lean` + `Run/Machine.lean` + `Run/Model.lean`.
    R1–R3 were re-proved in place (`Semantics.lean`, `Refinement.lean`,
    `BcModel.lean`); the census now reads 26 + 10 + 11 = 47 lines, against
    119 before.
* **C3: Reloc adopted.** Held-out 103 → 71 (−31%); extra components 41 → 30.
  * No refactors exist in this cluster.
  * Setup 115 lines. Break-even ≈ 10 of the ~40 components, at the measured
    ~11 lines saved per component.
  * Landed as `OCaml/Vm/Reloc.lean`, with H5–H7, HeapRepr and globals as
    library lemmas.
  * **Condition:** the real collector needs the `ScanCoherent` bridge plus the
    NoForgery and RememberedComplete premises, and the Forward_tag and
    Infix clauses (§2, L3′). These are now obligations of the Layer A
    minor-GC simulation.
* **C4: Membrane adopted; EffTree rejected.**
  * Membrane: held-out 73 → 57 (−22%). Bound-1000 probe: 1 line against the
    incumbent's 41, whose kernel work grows with the bound.
  * EffTree costs more than the incumbent (84 lines) and needs a 150-opcode
    bridge or a redefinition of `stepI`. Its locality theorem was cheap (36
    lines), but its real cost was tagged arithmetic, which it does not help.
    It stays on file for when heap-reading segments block symbolic reduction.
  * Landing Membrane, its `runN` duplicated the adopted C1 kernel's iterate
    (Law 3). It was rebased onto `Run.iter (bcK P)`; the proofs went through
    unchanged except for `some`→`.ok`. Landed as `OCaml/Logic/Symbolic.lean`
    + `OCaml/Programs/CountLoop.lean`, which proves the loop for any bound.
* **C2** (checker soundness, 7 members) was not targeted; it stays under
  the gate.

Enforcement:
* CLAUDE.md names each adopted route as mandatory for its task shape.
* `scripts/discipline_rules.tsv` gains O5 (no induction on a run relation),
  O6 (no unfolding `reloc` by hand) and O7 (no hand-listed `.succ (.mk rfl)`
  intermediate states).
* `abstractions/clusters.def` carries `adopted 2026-09-30` lines for C1, C3
  and C4, so the gate measures only post-adoption proofs.
* `scripts/check_all.sh` passes with 41 audited theorems.

Novel, worth writing up:
* the presentation interface (`ConsPres`/`ClosPres`), where a relation
  enters the run algebra by its constructors and inversion;
* the finding that a relocation law checked against its own idealised model
  validates the proofs' law and not the collector's (L3 vs L3′: 8,664 and
  3,123 counterexamples, and two runtime cases found in `minor_gc.c` by
  reading the source).

## 8. Round 1b: ship-your-interpreter's `Vsa/Lang` layer vs the incumbent (Layer A plumbing)

ship-your-interpreter (branch `exponentiate`, commit 3274bd70) offered a
language-parametric refinement layer (`Vsa/Lang`: `SmallStep`,
`ArmSim.simTotal`, `SimTotal.refinement`, `Refines.of_fillZero`). The
held-out suite was fixed and committed before either entrant started
(`abstractions/pilot/Pilot2.lean`, 42506b6):
* H10: Layer A observing only the exit code;
* H11: Layer A against the Iris model `bcModel`.

The refactor R4 is `Refinement.lean`'s five simulation proofs (55 lines).
Both worktrees were created at 42506b6 with the build copied in.

| entrant | setup | H10 + H11 | R4 (orig 55) | fails |
|---|---|---|---|---|
| Incumbent (existing tools + run kernel) | 10 (the converse `bcHalts_halts`, 7, + an iff) | 2 + 2 = **4** | 55 as scored; 45 with existing tools, no new lemma | 1 |
| LangLayer | 243 copied + 57 bridge written | 2 + 2 = **4** | **9** | 5 (all setup) |

**Decision: LangLayer not adopted.**
* The held-out cases tie (4 = 4), so the rule's first half ("held-out cases
  get cheaper") fails. The refactor saving (−46 lines) costs 300 new lines
  in this repository.
* The layer pays off with several language instances. This repository has
  one: about 40 lines per extra instance through the layer, per the entrant.
* Two findings go back upstream:
  * `Vsa/Lang/Runs.lean` re-proves machine run algebra by induction,
    duplicating the run kernel;
  * `Basic`/`SmallStep` trip discipline rule R7 (∃ count).

**Landed from the incumbent:**
* `Logic.bcHalts_halts` and `halts_iff_bcHalts`: the model and `BcSem` halt
  alike, by the run kernel's lockstep transport;
* `ocamlrun_refinement_exit` (H10) and `ocamlrun_refinement_bcModel` (H11)
  in `Theorems.lean`;
* the three shorter simulation proofs (`ocamlrun_refinement_of_sim`,
  `run_sim`, `simOfArms`: 45 → 35 lines).
