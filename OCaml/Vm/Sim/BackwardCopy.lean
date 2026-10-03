import OCaml.Vm.Sim.BackwardCopyMore
import OCaml.Vm.Sim.BackwardCopyLast

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim

/-- One concrete reverse-copy iteration, choosing its proved native branch. -/
theorem backward_copy_iteration {source target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : BackwardCopyRegion source target words initial) :
    Vsa.Logic.Triple (BackwardCopyAt source target words initial (i + 1))
      (BackwardCopyAt source target words initial i) := by
  intro c h
  have body : ∃ nb after, StepsN nb c after ∧ BackwardCopyAt source target words initial i after := by
    by_cases positive : 0 < i
    · exact backward_copy_more region h positive
    · exact backward_copy_last region h (by omega)
  obtain ⟨nb, after, steps, post⟩ := body
  exact ⟨after, OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp steps⟩, post⟩

/-- The actual APPTERM backward-copy loop terminates for every bounded word
count, including overlapping source/destination ranges. No iteration premise. -/
theorem backward_copy_run {source target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : BackwardCopyRegion source target words initial) :
    Vsa.Logic.Triple (BackwardCopyAt source target words initial words.length)
      (BackwardCopyAt source target words initial 0) :=
  backward_copy_loop region (fun _ => backward_copy_iteration region)

end OCaml.Vm.Sim
