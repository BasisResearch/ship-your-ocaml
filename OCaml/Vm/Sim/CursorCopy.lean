import OCaml.Vm.Sim.CursorCopyMore
import OCaml.Vm.Sim.CursorCopyLast

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim

/-- One actual GRAB copy iteration, selecting its generated native branch. -/
theorem cursor_copy_iteration {source target i : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : CursorCopyRegion source target words initial) :
    Vsa.Logic.Triple (fun c => CursorCopyAt source target words initial i c ∧ i < words.length)
      (CursorCopyAt source target words initial (i + 1)) := by
  intro c ⟨h, bound⟩
  have body : ∃ nb after, StepsN nb c after ∧ CursorCopyAt source target words initial (i + 1) after := by
    by_cases more : i + 1 < words.length
    · exact cursor_copy_more region h bound more
    · exact cursor_copy_last region h bound (by omega)
  obtain ⟨nb, after, steps, post⟩ := body
  exact ⟨after, OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp steps⟩, post⟩

/-- GRAB's actual forward-copy machine loop terminates and copies the saved
arguments. No iteration or execution premise remains. -/
theorem cursor_copy_run {source target : Nat} {words : List (BitVec 64)} {initial : Config}
    (region : CursorCopyRegion source target words initial) :
    Vsa.Logic.Triple (CursorCopyAt source target words initial 0)
      (CursorCopyAt source target words initial words.length) :=
  cursor_copy_loop region (fun _ => cursor_copy_iteration region)

end OCaml.Vm.Sim
