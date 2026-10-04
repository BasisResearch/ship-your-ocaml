import OCaml.Vm.Sim.CopyLogFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A loop's exact completed prefix, with one finite write block per iteration. -/
def groupedLog (groups : List (List WEntry)) (count : Nat) : List WEntry :=
  (groups.take count).flatten

theorem grouped_log_step (groups : List (List WEntry)) (i : Nat) (bound : i < groups.length) :
    groupedLog groups (i + 1) = groupedLog groups i ++ groups[i] := by
  simp only [groupedLog, List.take_succ_eq_append_getElem bound, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil]

theorem grouped_log_complete (groups : List (List WEntry)) : groupedLog groups groups.length = groups.flatten := by
  simp [groupedLog]

theorem grouped_log_sublist (groups : List (List WEntry)) (i : Nat) :
    (groupedLog groups i).Sublist groups.flatten := by
  conv => rhs; rw [← List.take_append_drop i groups, List.flatten_append]
  exact List.sublist_append_left _ _

/-- Reads during an iteration can use any initial prefix of its write block. -/
theorem grouped_partial_sublist (groups : List (List WEntry)) (i n : Nat) (bound : i < groups.length) :
    (groupedLog groups i ++ groups[i].take n).Sublist groups.flatten := by
  have part := (List.Sublist.refl (groupedLog groups i)).append (List.take_sublist n groups[i])
  rw [← grouped_log_step groups i bound] at part
  exact part.trans (grouped_log_sublist groups (i + 1))

theorem grouped_log_member {groups : List (List WEntry)} {i : Nat} {entry : WEntry}
    (bound : i < groups.length) (member : entry ∈ groups[i]) : entry ∈ groups.flatten :=
  List.mem_flatten.mpr ⟨groups[i], List.getElem_mem bound, member⟩

/-- One actual iteration advances both the exact grouped log and its image frame. -/
theorem grouped_log_advance {groups : List (List WEntry)} {i : Nat} {initial before after : Config}
    (bound : i < groups.length) (image : ExecutableImage before)
    (outside : ImageOutside groups.flatten)
    (memory : before.σ.mem = writeLog initial.σ.mem (groupedLog groups i))
    (stepMemory : after.σ.mem = writeLog before.σ.mem groups[i]) :
    ExecutableImage after ∧ after.σ.mem = writeLog initial.σ.mem (groupedLog groups (i + 1)) := by
  refine ⟨image_of_writeLog image (imageOutside_sublist
    (List.sublist_flatten_of_mem (List.getElem_mem bound)) outside) stepMemory, ?_⟩
  rw [stepMemory, memory, grouped_log_step groups i bound, writeLog_append]

end OCaml.Vm.Sim
