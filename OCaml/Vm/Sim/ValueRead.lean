import OCaml.Vm.Sim.StackPrefix

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Consecutive field arrays share the existing stack-prefix indexing law.
No stack geometry is assumed: the temporary high address is the array end. -/
theorem value_read_append {c : Config} {pl : Place} {base : Nat} {left right : List Val}
    (front : ∀ i v, left[i]? = some v → valWord pl v = some (word c (base + 8 * i)))
    (back : ∀ i v, right[i]? = some v →
      valWord pl v = some (word c (base + 8 * left.length + 8 * i))) :
    ∀ i v, (left ++ right)[i]? = some v → valWord pl v = some (word c (base + 8 * i)) := by
  have tail : StackRepr c pl (base + 8 * left.length)
      (base + 8 * (left.length + right.length)) right := ⟨by omega, back⟩
  exact (stack_prepend tail rfl front).2

/-- One metadata field joins a represented consecutive array. -/
theorem value_read_cons {c : Config} {pl : Place} {base : Nat} {head : Val} {tail : List Val}
    (front : valWord pl head = some (word c base))
    (back : ∀ i v, tail[i]? = some v → valWord pl v = some (word c (base + 8 + 8 * i))) :
    ∀ i v, (head :: tail)[i]? = some v → valWord pl v = some (word c (base + 8 * i)) := by
  apply value_read_append (left := [head])
  · intro i v selected
    cases i with
    | zero => cases selected; exact front
    | succ i => simp at selected
  · exact back

end OCaml.Vm.Sim
