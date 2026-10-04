import OCaml.Vm.Sim.SdivPosPosPrepare
import OCaml.Vm.Sim.SdivPosNegPrepare
import OCaml.Vm.Sim.SdivNegPosPrepare
import OCaml.Vm.Sim.SdivNegNegPrepare
import OCaml.Vm.Sim.SmodPosPosPrepare
import OCaml.Vm.Sim.SmodPosNegPrepare
import OCaml.Vm.Sim.SmodNegPosPrepare
import OCaml.Vm.Sim.SmodNegNegPrepare
import OCaml.Vm.Sim.SdivNegateFinish
import OCaml.Vm.Sim.SmodPosReturnFinish
import OCaml.Vm.Sim.SmodNegReturnFinish

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def divisionEntry : DivisionKind → BitVec 64
  | .quotient => 0x80037298#64
  | .remainder => 0x8003731c#64

/-- Exhaust the operand signs using the eight generated normalization paths. -/
theorem signed_division_prepare (kind : DivisionKind) {c : Config} {x y ra : BitVec 64}
    (input : SignedDivisionInput x y ra c) (pc : pcOf c = some (divisionEntry kind)) :
    ∃ n after, StepsN n c after ∧ SignedDivisionPrepared kind c x y ra after := by
  cases kind <;> cases hx : x.msb <;> cases hy : y.msb
  · exact sdiv_pos_pos_prepare input pc hx hy
  · exact sdiv_pos_neg_prepare input pc hx hy
  · exact sdiv_neg_pos_prepare input pc hx hy
  · exact sdiv_neg_neg_prepare input pc hx hy
  · exact smod_pos_pos_prepare input pc hx hy
  · exact smod_pos_neg_prepare input pc hx hy
  · exact smod_neg_pos_prepare input pc hx hy
  · exact smod_neg_neg_prepare input pc hx hy

/-- The core either already returned, or reaches one generated native fixup. -/
theorem signed_division_finish {kind : DivisionKind} {before c : Config} {x y ra : BitVec 64}
    (h : SignedDivisionDivided kind before x y ra c) :
    ∃ after, Steps c after ∧ SignedDivisionPost before ra (divisionResult kind x y) after := by
  cases kind with
  | quotient =>
    cases sign : divisionNegative .quotient x y with
    | false => exact ⟨c, Steps.refl c, signed_division_done h sign⟩
    | true =>
      obtain ⟨n, after, run, post⟩ := sdiv_negate_finish h sign
      exact ⟨after, run.toSteps, post⟩
  | remainder =>
    cases sign : divisionNegative .remainder x y with
    | false =>
      obtain ⟨n, after, run, post⟩ := smod_pos_return_finish h sign
      exact ⟨after, run.toSteps, post⟩
    | true =>
      obtain ⟨n, after, run, post⟩ := smod_neg_return_finish h sign
      exact ⟨after, run.toSteps, post⟩

/-- Total signed libgcc division and remainder summaries for nonzero divisors.
All machine normalization and return spans are generated; the unsigned loop
is the existing proved core. The most-negative native word is included. -/
theorem signed_division_summary (kind : DivisionKind) {before : Config} {x y ra : BitVec 64}
    (input : SignedDivisionInput x y ra before) :
    FnSummary (divisionEntry kind) (fun c => c = before)
      (SignedDivisionPost before ra (divisionResult kind x y)) := by
  constructor
  rintro c ⟨pc, rfl⟩
  obtain ⟨n, core, prefixRun, prepared⟩ := signed_division_prepare kind input pc
  obtain ⟨done, coreRun, divided⟩ := signed_division_core prepared
  obtain ⟨after, suffixRun, post⟩ := signed_division_finish divided
  exact ⟨after, prefixRun.toSteps.trans (coreRun.trans suffixRun), post⟩

end OCaml.Vm.Sim
