# LangLayer: bake-off round 1b result

Entrant: ship-your-interpreter's language-parametric refinement layer
`Vsa/Lang/{Basic,Runs,SmallStep,Densify}.lean` (syi-exp `exponentiate`,
3274bd70), copied verbatim into `Vsa/Lang/`. The bridge and the proofs are in
`abstractions/pilot/LangLayer.lean`.

## Table

Proof lines are non-blank and non-comment, counted from the `:=` onward. Setup
counts every code line of section 1. The five R4 originals total 55 proof lines
(13/7/15/17/3).

| Item | Proof lines | Wall time | Failed checks |
| --- | --- | --- | --- |
| setup (bridge, written here) | 57 | 07:59:23 → 08:02:01 (2m38s) | 5 |
| `h10` | 2 | 08:00:20 → 08:02:01 | 0 |
| `h11` | 2 | 08:00:20 → 08:02:01 | 0 |
| `ocamlrun_refinement_of_sim_r` | 2 (was 13) | 08:00:20 → 08:02:01 | 0 |
| `ocamlrun_refinement_fillZero_r` | 2 (was 7) | 08:00:20 → 08:02:01 | 0 |
| `run_sim_r` | 2 (was 15) | 08:00:20 → 08:02:01 | 0 |
| `simOfArms_r` | 1 (was 17) | 08:00:20 → 08:02:01 | 0 |
| `ocamlrun_refinement_of_arms_r` | 2 (was 3) | 08:00:20 → 08:02:01 | 2 |

How to read the times and failures:

* Every item was written in one edit (08:00:20). The item's own proof term
  never changed after that.
* Every failed check was a setup failure. The two failures listed for
  `ocamlrun_refinement_of_arms_r` cascaded from setup: the `(bcLang B).Total`
  instance was missing, so its implicit `B` could not be elaborated.
* Until 08:02:01 all seven items depended on sorried setup. The item times
  therefore end at the first axiom-clean check.
* All seven items have axioms {propext, Classical.choice, Quot.sound}.

The R4 re-proofs total 9 proof lines, against 55 originally.

## Setup split

* **Copied from upstream:** 243 code lines (378 raw):
  * `Basic` 94
  * `Runs` 31
  * `SmallStep` 94
  * `Densify` 24

  All four built unchanged against this repo's retargeted
  `Vsa.Machine`/`Vsa.Densify`, with no edits (`lake build Vsa.Lang.SmallStep
  Vsa.Lang.Densify`). None of the parameters that PORTING.md §7 lists as
  hard-wired (`tohostAddr`, `initMisa`, `gp`, image ranges, console site,
  layout) is referenced by `Vsa/Lang`: it imports only `Halts`, `Diverges`,
  `StepsN`, `Steps` and `fillZero`.
* **Written here:** 57 code lines. These are:
  * `bcSS`, `BcSem` as a `SmallStep` (`Next := Step`, the graph of `bcK`;
    `Final P s e out := ∃ w, step P s = .halt e w ∧ bytesToString w.console = out`);
  * `ss_pres`, its `ConsPres` presentation. From it `ss_stepsN_iff` follows
    through `bcK_graph` and `stepsN_iff`, which is the run-kernel route with no
    induction;
  * `ss_reach_iff`, `ss_halts_iff` and `ss_diverges_iff`;
  * the side condition `BcFits B P := Good P ∧ Fits B P`, with `progress`;
  * `bcLang B := bcSS.toLang (BcFits B) _`;
  * `armSim`, the adapter at the three `ArmSim` use sites (entry, next, halt);
  * `simTotal_of_sim` and `sim_of_simTotal`;
  * `refinement_of_refines`;
  * `layerA` (`ArmSim.simTotal` followed by `SimTotal.refinement`);
  * `bcModel_halts_iff`. `halts_bcHalts` existed only one way; the converse is
    a lockstep `iter_transport` over `bcModel_square`.

## Surprises

* `bcSS` had to be an `abbrev`. With `def`, instance synthesis at reducible
  transparency could not see `bcSS.Prog = Prog`, so `(bcLang B).Total`
  (upstream's `instTotalToLang`) failed. That one failure cascaded into every
  `SimTotal` use.
* Elaborating `StepsN.zero` against `bcSS.StepsN P 0 c c` also failed, even
  with `abbrev`. It needed `@Vsa.Lang.SmallStep.StepsN.zero bcSS P c`; `.succ`
  and the `match` inversion elaborated fine.
* H10 and H11 needed no new layer construct. `toLang` sets `Obs := True`, so
  both are `exists_congr` or `iff.trans` over `RefinesTotal.halts`. H11 cost
  only the missing converse of `halts_bcHalts`.
* `run_sim` is literally `ArmSim.run`, and `simOfArms` is literally
  `ArmSim.simTotal` behind the adapter. The incumbent's `Plus` and the
  layer's `Plus` are the same definition, so `entry` passes through as is.
* **Discipline gate:** `python3 scripts/check_discipline.py` now fails with
  R7 (`COUNT>8:∃`) on the copied `Vsa/Lang/Basic.lean` (9) and
  `Vsa/Lang/SmallStep.lean` (12).
  * These are verbatim copies. The fix is to list them in
    `scripts/discipline_grandfather.txt`, which the protocol does not allow
    this entrant to touch.
  * `Vsa/Lang/Runs.lean` also re-proves machine run algebra by induction
    (`steps_trans`, `stepsN_append`, `stepsN_prefix`). This duplicates
    `OCaml/Run/Machine.lean`'s `vsa_*_iff` kernel laws. O5 does not fire only
    because O5 is scoped to `OCaml/*`. If adopted, `Runs` should be restated
    as kernel corollaries.

## Next case of this cluster

* **Another observation of `BcSem`:** about 2 lines. Examples are exit-only or
  output-only halts, or the `bcModel` halts. Each is `exists_congr`/`trans`
  over `layerA`'s `RefinesTotal.halts`, plus one lockstep lemma if it goes
  through another kernel.
* **Another language instance:** about 40 lines, the same shape as this
  bridge. Examples are Lua's `BcSem`, or `bcModel` as a `SmallStep`. The cost
  is a `SmallStep` value, one `ConsPres` presentation, the three
  reach/halts/diverges iffs, `Progress` from `Good`, and an `ArmSim` adapter.
  The adapter and the two sim converters (about 15 lines) disappear if
  `OCaml.ArmSim`/`OcamlrunSim` are restated as `bcSS.ArmSim`/`SimTotal`
  directly.
