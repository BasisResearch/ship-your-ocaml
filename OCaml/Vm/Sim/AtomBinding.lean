import OCaml.Vm.Sim.ArmInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- Atom pointers use the allocated table named by the runtime global. -/
theorem atom_word_of_binding {pl : Place} {c : Config}
    (binding : (word c Layout.sym_caml_atom_table).toNat = pl.atomBase) (tag : Nat) :
    valWord pl (.atom tag) = some (word c Layout.sym_caml_atom_table + BitVec.ofNat 64 (8 * tag + 8)) := by
  simp only [valWord, ← binding, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end OCaml.Vm.Sim
