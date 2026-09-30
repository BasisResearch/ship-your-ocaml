# Pilot 1b: incumbent entrant (`Incumbent1b`)

File: `abstractions/pilot/Incumbent1b.lean` (imports `Pilot2`). Uses only
what the repository has: `OCaml/Refinement.lean` (`ocamlrun_refinement_of_arms`),
the run kernel (`Run.haltsK_iff`, `Run.mm_halts_iff`, `Run.iter_transport`)
and `OCaml/Logic/BcModel.lean` (`bcModel_square`, `halts_bcHalts`). No new
abstraction layer. All theorems check with axioms ⊆ {propext,
Classical.choice, Quot.sound}; `scripts/check_discipline.py` is OK.

Lines are non-blank, non-comment lines of the whole declaration (statement
included, docstrings excluded), the counting that gives the 13/7/15/17/3
figure for the originals.

| Item | Lines | Wall time | Failed checks |
|---|---|---|---|
| Setup: `bcHalts_halts` (converse of `halts_bcHalts`, through the same lockstep square) | 7 | ~70 s (07:58:00 → 07:59:10) | 0 |
| Setup: `halts_iff_bcHalts` | 3 | (same check) | 0 |
| H10 | 2 | (same check) | 0 |
| H11 | 2 | (same check) | 0 |
| R4 `ocamlrun_refinement_of_sim` | 13 (as is) | — | — |
| R4 `ocamlrun_refinement_fillZero` | 7 (as is) | — | — |
| R4 `run_sim` | 15 (as is) | — | — |
| R4 `simOfArms` | 17 (as is) | — | — |
| R4 `ocamlrun_refinement_of_arms` | 3 (as is) | — | — |
| **R4 total (incumbent number)** | **55** | — | — |

Setup total: 10 lines, all written here, 0 copied from upstream.

## R4 with the repository's own tools (experiment, not the incumbent number)

Re-proved with identical statements as `*_r` in the same file:

| Theorem | Original | Shortened | How | Wall time | Failed checks |
|---|---|---|---|---|---|
| `ocamlrun_refinement_of_sim` | 13 | 9 | case-split `halts_or_diverges` once, outside the two iffs; `obtain ⟨rfl, rfl⟩` instead of two `subst` | 6 s | 0 |
| `ocamlrun_refinement_fillZero` | 7 | 7 | already minimal | — | — |
| `run_sim` | 15 | 13 | `obtain ⟨e⟩ := st`; inline the `Reach` witness into `ih` | 17 s | 1 (`hr.1`: `Reach` is an `∃`, so no projection) |
| `simOfArms` | 17 | 13 | `ho ▸` into `Halts.of_steps`; `hd' ▸` into `StepsN.prefix'` | 6 s | 0 |
| `ocamlrun_refinement_of_arms` | 3 | 3 | already minimal | — | — |
| Total | 55 | 45 | −10 lines (−18%), all local tidying, no new lemma | | |

The remaining redundancy: `simOfArms`'s two fields share the same
entry + `run_sim` prefix (2 lines each). Removing it takes a named lemma
("from `Loaded`, every `BcSem` run of `k` steps is shadowed by ≥ k machine
steps"), which is a new abstraction and so outside the incumbent's rules.

## What surprised me

* H10 and H11 are corollaries of the one refinement theorem: H10 is
  `exists_congr` over it, and H11 composes it with `bcModel ↔ BcSem`.
* The missing converse `BcHalts → VsaIris.Halts (bcModel P)` cost 7 lines.
  It is the mirror of `halts_bcHalts`: the square `bcModel_square` and
  `iter_transport` already carry the halting outcome forward, so the proof
  is `iter_transport … |>.trans (by rw [hn]; rfl)` plus the adapters. The
  run kernel made this direction as cheap as the landed one.
* H10 and H11 had no failed checks. The only failure in the session was a
  shape slip in the optional R4 tidying.

## The next case of this cluster

About 2–5 lines per case, for example `BcDiverges ↔ VsaIris.Diverges`
(bcModel P) or a halting observation with the file system. Every such
observation is a projection of `OcamlrunRefinement` composed with an
adapter iff. The adapter comes from a kernel square (`iter_transport` plus
`mapOut_ok`/`mapOut_error`). A new observation that `BcSem`'s kernel
outcome does not determine would need the refinement itself restated.
