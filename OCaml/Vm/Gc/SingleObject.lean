import OCaml.Vm.Reloc

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Reloc

/-- Assemble a singleton object from its color-insensitive header and value
atom. Both forwarding and fixed-value terminal branches use this interface. -/
theorem single_object_of_payload {c pl cp a tag value}
    (header : HeaderOk (word c (a - Layout.header_bytes)) 1 tag)
    (field : (Eqv.val value id).P pl a c) :
    ObjAt c pl cp a (.block tag [value]) := by
  refine ⟨header,?_⟩
  intro i v hi
  cases i with
  | zero =>
    have equal : value = v := Option.some.inj hi
    subst v
    simpa [Eqv.val] using field
  | succ i => simp at hi

end OCaml.Vm.Gc
