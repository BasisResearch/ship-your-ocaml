import Vsa.Sim.StepFrameOut

namespace Vsa.Sim
open LeanRV64DExecutable Vsa.Machine

/-- Change a composed frame's write list using a finite inclusion certificate.
Generators use this to remove repeated step noise before exporting a long span. -/
theorem StepFrameOut.widen {written allowed : List Register} {before after : MState}
    (h : StepFrameOut written before after)
    (subset : ∀ r ∈ written, r ∈ allowed) : StepFrameOut allowed before after where
  out := h.out
  frame := fun r avoid => h.frame r (fun w hw => avoid w (subset w hw))

/-- Reflect a finite membership check instead of enumerating every Register. -/
theorem StepFrameOut.widenChecked {written allowed : List Register} {before after : MState}
    (h : StepFrameOut written before after)
    (check : written.all (fun r => decide (r ∈ allowed)) = true) :
    StepFrameOut allowed before after :=
  h.widen (fun r hr => of_decide_eq_true (List.all_eq_true.mp check r hr))

end Vsa.Sim
