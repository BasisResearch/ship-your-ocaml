import OCaml.Run.Kernel
import VsaIris.Adequacy

/-!
# Any `VsaIris.MachineModel` as a run kernel

`mmK M` presents `M.step` as a kernel step function
(`OCaml/Run/Kernel.lean`); `ReachesN` and `Reaches` enter by their
presentations. The model-level run laws (unique halting, `Reaches` as
`∃ n, ReachesN`) are kernel corollaries, proved here once for every model
(discipline rule O5).
-/

namespace OCaml.Run

/-- A machine model as a kernel; outcome `none` is `stuck`. -/
def mmK (M : VsaIris.MachineModel) (σ : M.State) : Except (Option (Nat × String)) M.State :=
  match M.step σ with
  | .next σ' => .ok σ'
  | .halt e out => .error (some (e, out))
  | .stuck => .error none

theorem mmK_graph (M : VsaIris.MachineModel) : Graph (mmK M) (fun a b => M.step a = .next b) :=
  ⟨fun {a _} => by unfold mmK; split <;> simp_all⟩

theorem mmK_halt {M : VsaIris.MachineModel} {σ : M.State} {e : Nat} {out : String} :
    M.step σ = .halt e out ↔ mmK M σ = .error (some (e, out)) := by unfold mmK; split <;> simp_all

theorem reachesN_pres (M : VsaIris.MachineModel) :
    ConsPres (fun a b => M.step a = .next b) (VsaIris.ReachesN M) :=
  ⟨.zero, .succ, fun h => by cases h <;> simp_all⟩

theorem reaches_pres (M : VsaIris.MachineModel) :
    ClosPres (fun a b => M.step a = .next b) (VsaIris.Reaches M) :=
  -- discipline: allow(O5-run-induction) the ClosPres presentation's induction principle
  ⟨.refl, .step, fun _ h0 h1 _ _ h => by induction h with
    | refl => exact h0 _
    | step s r ih => exact h1 s r ih⟩

theorem mm_halts_iff {M : VsaIris.MachineModel} {σ : M.State} {e : Nat} {out : String} :
    VsaIris.Halts M σ e out ↔ HaltsK (mmK M) σ (some (e, out)) := by
  simp only [VsaIris.Halts, HaltsK, (reaches_pres M).iff (mmK_graph M), mmK_halt]

/-- A machine model halts at most one way. -/
theorem mm_halts_unique {M : VsaIris.MachineModel} {σ : M.State} {e e' : Nat} {out out' : String}
    (h : VsaIris.Halts M σ e out) (h' : VsaIris.Halts M σ e' out') : e = e' ∧ out = out' := by
  cases (mm_halts_iff.1 h).unique (mm_halts_iff.1 h'); exact ⟨rfl, rfl⟩

/-- `Reaches` is "some number of steps". -/
theorem mm_reaches_iff (M : VsaIris.MachineModel) (a b : M.State) :
    VsaIris.Reaches M a b ↔ ∃ n, VsaIris.ReachesN M n a b :=
  ((reaches_pres M).iff (mmK_graph M)).trans
    (exists_congr fun _ => ((reachesN_pres M).iff (mmK_graph M)).symm)

end OCaml.Run
