import Vsa.Sim.RegPins

namespace Vsa.Sim
open Vsa.Machine

/-- Read a pin by its finite list index, without exposing conjunction positions.
Generators compute the index from register names; the bound inspects only
list length, never the symbolic register values. -/
theorem PinsHold.get {σ : MState} {L : List Pin} (h : PinsHold σ L)
    (i : Fin L.length) : σ.regs.get? L[i].1 = some L[i].2 := by
  revert h i
  induction L with
  | nil => intro _ i; exact Fin.elim0 i
  | cons p rest ih =>
    intro h i
    exact Fin.cases h.1 (fun j => ih h.2 j) i

end Vsa.Sim
