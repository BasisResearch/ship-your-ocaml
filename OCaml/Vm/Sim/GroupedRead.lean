import OCaml.Vm.Sim.GroupedLog
import OCaml.Vm.Sim.ClosureLayout

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A grouped footprint is outside a range when every iteration is outside. -/
theorem grouped_log_outside {groups : List (List WEntry)} {a n : Nat}
    (outside : ∀ group ∈ groups, OutLRange group a n) :
    OutLRange groups.flatten a n := by
  induction groups with
  | nil => trivial
  | cons group groups ih =>
    exact outLRange_append (outside group (by simp))
      (ih (fun g member => outside g (by simp [member])))

/-- Index-based separation for the suffix after a selected iteration. -/
theorem grouped_suffix_outside {groups : List (List WEntry)} {i a n : Nat}
    (outside : ∀ j (bound : j < groups.length), i < j → OutLRange groups[j] a n) :
    OutLRange (groups.drop (i + 1)).flatten a n := by
  apply grouped_log_outside
  intro group member
  obtain ⟨j, bound, selected⟩ := List.mem_drop_iff_getElem.mp member
  rw [← selected]
  exact outside (i + 1 + j) (by omega) (by omega)

/-- A selected iteration's readback survives every later iteration. Earlier
writes are arbitrary; callers prove only local readback and suffix separation. -/
theorem grouped_log_read (groups : List (List WEntry)) (i a : Nat) (w : BitVec 64)
    (bound : i < groups.length)
    (read : ∀ memory : Std.ExtHashMap Nat (BitVec 8),
      bytesT (writeLog memory groups[i]) a 8 = w)
    (outside : OutLRange (groups.drop (i + 1)).flatten a 8)
    (memory : Std.ExtHashMap Nat (BitVec 8)) :
    bytesT (writeLog memory groups.flatten) a 8 = w := by
  have split : groups.flatten =
      (groupedLog groups i ++ groups[i]) ++ (groups.drop (i + 1)).flatten := by
    rw [← grouped_log_step groups i bound]
    exact (congrArg List.flatten (List.take_append_drop (i + 1) groups)).symm.trans
      (by rw [List.flatten_append]; rfl)
  rw [split, writeLog_append, bytesT_writeLog_out _ outside, writeLog_append]
  exact read _

end OCaml.Vm.Sim
