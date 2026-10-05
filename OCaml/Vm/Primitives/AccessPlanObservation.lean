import OCaml.Vm.Primitives.AccessPlan
import OCaml.Vm.Primitives.WriteLogObservation

namespace OCaml.Vm.Primitives
open Vsa.Sim

/-- Data-access facts depend on total byte reads, never map presence. -/
theorem memFacts_observed {m m' L bs a} (memory : Vsa.Densify.MemEqv m' m)
    (h : MemFacts m L bs a) : MemFacts m' L bs a := by
  have observe : ∀ x : Nat, (m'[x]?).getD 0 = (m[x]?).getD 0 := fun x => memory x
  cases kind : a.kind <;> simp only [MemFacts, kind, LPins4, LPins8] at h ⊢
  all_goals simpa only [observe] using h

/-- Symbolic scalar stores preserve total-byte equality. -/
theorem stepMemM_observed {m m' a L} (memory : Vsa.Densify.MemEqv m' m) :
    Vsa.Densify.MemEqv (stepMemM m' a L) (stepMemM m a L) := by
  cases kind : a.kind <;> simp only [stepMemM, kind]
  all_goals first | exact memory | exact memory.applyW _

/-- Transport a finite access plan across total-byte equality. The induction
is on the generated instruction syntax, not a machine execution. -/
theorem AccessPlan.observed_transport {m m' L loads body}
    (h : AccessPlan m L loads body) (memory : Vsa.Densify.MemEqv m' m) :
    AccessPlan m' L loads body := by
  induction body generalizing m m' L loads with
  | nil => trivial
  | cons a rest ih =>
    exact ⟨memFacts_observed memory h.1, ih h.2 (stepMemM_observed memory)⟩

end OCaml.Vm.Primitives
