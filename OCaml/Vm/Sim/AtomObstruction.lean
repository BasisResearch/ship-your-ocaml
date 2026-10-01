import OCaml.Vm.Sim.AtomBinding
import OCaml.Vm.Boot.WhileMinHeapObjects

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- The legacy representation mistakenly used the address of the pointer global. -/
def legacyAtomWord (tag : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (Layout.sym_caml_atom_table + 8 * tag + 8)

/-- The captured startup table demonstrates why the old atom representation
cannot describe the native ATOM0 result. This is a word-level obstruction,
not a whole-program machine execution claim. -/
theorem captured_atom_not_legacy {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem initial Boot.WhileMinLog.log)) :
    word c Layout.sym_caml_atom_table + 8#64 ≠ legacyAtomWord 0 := by
  rw [Boot.WhileMinHeap.read_atom_table memory]
  decide +kernel

end OCaml.Vm.Sim
