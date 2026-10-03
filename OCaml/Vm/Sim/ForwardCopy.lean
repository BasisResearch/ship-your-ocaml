import OCaml.Vm.Sim.ForwardCopyMore
import OCaml.Vm.Sim.ForwardCopyLast

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim

/-- One actual RESTART copy iteration, selecting its generated native branch. -/
theorem forward_copy_iteration {a target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial) :
    Vsa.Logic.Triple (fun c => ForwardCopyAt a target words initial i c ∧ i < words.length)
      (ForwardCopyAt a target words initial (i + 1)) := by
  intro c ⟨h, bound⟩
  have body : ∃ nb after, StepsN nb c after ∧ ForwardCopyAt a target words initial (i + 1) after := by
    by_cases more : i + 1 < words.length
    · exact forward_copy_more region h bound more
    · exact forward_copy_last region h bound (by omega)
  obtain ⟨nb, after, steps, post⟩ := body
  exact ⟨after, OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp steps⟩, post⟩

/-- RESTART's actual forward-copy machine loop terminates and copies the saved
closure fields. No iteration or execution premise remains. -/
theorem forward_copy_run {a target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : ForwardCopyRegion a target words initial) :
    Vsa.Logic.Triple (ForwardCopyAt a target words initial 0)
      (ForwardCopyAt a target words initial words.length) :=
  forward_copy_loop region (fun _ => forward_copy_iteration region)

end OCaml.Vm.Sim
