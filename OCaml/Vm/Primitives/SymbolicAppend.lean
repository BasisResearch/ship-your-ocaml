import Vsa.Sim.SegEval

namespace Vsa.Sim

/-- Algebra of the finite symbolic evaluator's instruction lists; this is
not induction over machine execution. It permits bounded generated chunks. -/
theorem runGM_append (xs ys : List MInstr) (R : GRegs) (loads : List (List (BitVec 8))) :
    runGM (xs ++ ys) R loads = runGM ys (runGM xs R loads) (ldsRunM xs loads) := by
  induction xs generalizing R loads with
  | nil => rfl
  | cons a xs ih => simpa only [List.cons_append, runGM, ldsRunM] using ih (stepGM a R (loads.headD [])) (stepLdsM a.kind loads)

/-- The symbolic store trace factors at any instruction-list boundary. -/
theorem wlogM_append (xs ys : List MInstr) (R : GRegs) (loads : List (List (BitVec 8))) :
    wlogM (xs ++ ys) R loads = wlogM xs R loads ++ wlogM ys (runGM xs R loads) (ldsRunM xs loads) := by
  induction xs generalizing R loads with
  | nil => rfl
  | cons a xs ih =>
    cases kind : a.kind <;> simp [List.cons_append, wlogM, runGM, ldsRunM, kind, ih, stepGM, stepLdsM]

end Vsa.Sim
