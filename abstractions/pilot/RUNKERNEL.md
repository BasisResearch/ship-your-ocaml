# RunKernel: pilot bake-off report

File: `abstractions/pilot/RunKernel.lean`. It imports `Pilot`, compiled with
`lake env lean -o .lake/build/lib/lean/Pilot.olean abstractions/pilot/Pilot.lean`.
The `riscv-lean/*/.lake` build directories also had to be copied from the
main checkout. The file checks with zero errors and zero `sorry`. Every
theorem's axioms are ⊆ {propext, Classical.choice, Quot.sound}; `h1` uses
only {propext, Quot.sound}.

## Design choice

The kernel is generic over `f : C → Except O C`, where `.ok` means continue
and `.error` means done. `Except` is core's two-constructor sum and already
has `bind`. The alternative was to state the kernel over
`VsaIris.StepResult`, but `Vsa.Machine`'s `Halted` carries the final Sail
state rather than a string, so that route would have lost information.
Instead, each system gets a small adapter:

* `mmK` for any `VsaIris.MachineModel`, with outcome `Option (Nat × String)`;
* `bcK` for `BcSem`, with the whole `Res` as outcome;
* `vsaK` for the RISC-V `Config`, with outcome `Option (Nat × MState)`.

The trichotomy is proved unconditionally (`halts_or_div`) and in the
`Bad`-parametrised form (`div_iff_not_halts`).

## Measurements

Lines are non-blank, non-comment proof lines, counted from the statement
line to the end of the proof. Failed attempts count `lake env lean` runs
that reported an error for that item.

| Item | Lines | Wall time | Failed attempts |
|---|---|---|---|
| **Setup: generic kernel** (`iter`, shift/snoc/absorb/unique/prefix/stop, `HaltsK`/`DivK`/`Reach`, trichotomy, `Graph`, `ConsPres`/`SnocPres`/`ClosPres` with `.iff`, `mapOut` + `iter_transport`) | 155 | 05:17→05:24 (7 min) | 2 |
| **Setup: adapters** (`mmK`, `bcK`, `vsaK` + graphs + presentations of `ReachesN`, `Reaches`, BcSem `StepsN`, `Vsa.Machine.StepsN`/`Steps`) | 50 | (same run as the kernel) | (same 2) |
| **Setup: per-system bridges** (`bc_iff`, `bcDiv_iff`, `bcHalts_iff`, `good_halt`, `gBc`, `bcModel_square`, `vsa_iffN/S`, `vsaDiv_iff`, `vsaHalts_iff`) | 35 | 05:25→05:39* | 0 |
| **Setup total** | **240** | | 2 |
| h1 | 2 | 05:25→05:39* | 0 |
| h2 | 2 | ″ | 0 |
| h3 | 6 | ″ | 0 |
| h4 | 12 | ″ | 1 (anonymous-constructor witness `_` inferred as `none`) |
| R1 `StepsN.det_k` | 3 | ″ | 0 |
| R1 `StepsN.snoc_k` | 3 | ″ | 0 |
| R1 `StepsN.stop_k` | 3 | ″ | 0 |
| R1 `halts_or_diverges_k` | 6 | ″ | 0 |
| R1 `BcHalts.not_diverges_k` | 3 | ″ | 0 |
| R1 `StepsN.prefix_k` | 3 | ″ | 0 |
| R1 `BcHalts.det_k` | 4 | ″ | 1 (name shadowing under `obtain … rfl`) |
| **R1 total** | **25** (original 76) | | 1 |
| R2 `StepsN.append_k` | 3 | ″ | 0 |
| R2 `Steps.trans'_k` | 2 | ″ | 0 |
| R2 `Halts.of_steps_k` | 3 | ″ | 0 |
| R2 `StepsN.prefix'_k` | 2 | ″ | 0 |
| **R2 total** | **10** (original 22) | | 0 |
| R3 `reaches_stepsN_k` | 5 | ″ | 1 (`Bytecode.StepsN` needs `namespace OCaml.Logic`, as in the original) |
| R3 `halts_bcHalts_k` | 6 | ″ | 0 |
| **R3 total** | **11** (original 21) | | 1 |
| **H1–H4 total** | **22** | | 1 |

\* The bridges, H1–H4 and R1–R3 were written in one batch at 05:25, then
checked. About 12 of those 14 minutes were spent waiting for the memory gate
(available memory was 18 GB, below the 25 GB threshold). Active work was
about 2 minutes plus one fix round at 05:38–05:39. Total wall time from the
first edit to the final check was about 22 minutes.

Summary:
* Per-case lines: 22 for H1–H4 and 46 for R1–R3, against the original 119
  for R1–R3.
* Setup: 240 lines, of which 155 are the generic kernel.

## Surprises

* The trichotomy needs no `Bad` parameter at the kernel level:
  `DivK ↔ ¬ ∃ o, HaltsK o` always holds. `Bad` only matters when converting
  the client's `Halts`, which filters outcomes. Both H3 and H4 therefore
  reduce to a "never Bad" lemma plus two outcome-shape `rcases`.
* `Good P ⇒ outcomes are halts` (`good_halt`) is shared by H3 and
  `halts_or_diverges`. Without it this would have been the one duplicated
  argument.
* `vsaK` matches on `(Vsa.stepOnce …).run σ` without ever evaluating the
  Sail state. `split` is enough for `Graph` and `Halted`, and there was no
  whnf trouble.
* No existing relation is snoc-style, so `SnocPres` is unused setup
  (~20 lines).
* `ConsPres.inv` is the same one-liner for every inductive `StepsN`/
  `ReachesN`:
  `fun h => by cases h with | zero => .inl ⟨rfl,rfl⟩ | succ s r => .inr ⟨_,_,rfl,s,r⟩`.
  For `ReachesN`, `by cases h <;> simp_all` also worked.

## Cost of the next case in the cluster

* **A new step relation or system** (e.g. a new `MachineModel`, or a LocalRun
  variant): about 15–25 lines. That is one adapter `def` (3–5 lines), a
  `Graph` (2 lines), one presentation per run relation (2–4 lines each),
  and `Halts`/`Div` bridges (3–4 lines each). Every run law (det, snoc,
  prefix, append, trans, halting uniqueness, trichotomy) then costs 2–4
  lines, as the table shows.
* **A new instance of an existing `MachineModel`**: 0 setup. `mmK`,
  `mm_halts_iff`, `reaches_pres` and `reachesN_pres` are generic in `M`
  (H1 and H2 are the evidence).
* **A new lossy refinement square** (another model collapsing outcomes):
  one outcome map `g` plus a square lemma (about 3 lines, `cases … <;> rfl`).
  Transported facts then cost about 5 lines each, as in R3.
* **Out of scope for this abstraction:** a new opcode or loop (H8/H9) and
  the GC relocation cases (H5–H7). This kernel says nothing about the
  contents of a step.
