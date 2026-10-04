import Vsa.Sim.FrameWriteSet
import Vsa.Sim.RegPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A generated span's register frame transports a complete metadata bundle. -/
theorem frame_pins {before after : MState} {written : List Register} {pins : List Pin}
    (frame : StepFrameOut written before after)
    (holds : PinsHold before pins)
    (avoid : ∀ r ∈ pins.map Sigma.fst, ∀ w ∈ written, (w == r) = false) : PinsHold after pins := by
  induction pins with
  | nil => trivial
  | cons pin pins ih =>
    exact ⟨(frame.frame pin.1 (avoid _ (by simp))).trans holds.1,
      ih holds.2 (fun r hr => avoid r (by simp [hr]))⟩

end OCaml.Vm.Sim
