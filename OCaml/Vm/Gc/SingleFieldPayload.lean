import OCaml.Vm.Gc.SingleFieldReturn
import OCaml.Vm.Gc.SingleObject

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives Reloc

/-- An immediate or rejected non-young child is stored unchanged by the
actual terminal route. If the final relocation fixes that typed value, the
field is represented under the final placement. -/
theorem Returned.payload_fixed {q root sp before after pl cp tag value μ}
    (post : Returned q root sp before after)
    (object : ObjAt before pl cp q.source.toNat (.block tag [value]))
    (rootOutside : OutLRange [(root.toNat,8,q.target)] q.source.toNat 8)
    (fixed : relocWord μ pl value (word before q.source.toNat) = word before q.source.toNat) :
    (Eqv.val value id).P (reloc μ pl) q.target.toNat after := by
  apply single_field_relocated object
  rw [fixed,post.value,child_original rootOutside]

/-- Non-pointer terminal fields are stable under every final placement. -/
theorem Returned.payload_nonpointer {q root sp before after pl cp tag value μ}
    (post : Returned q root sp before after)
    (object : ObjAt before pl cp q.source.toNat (.block tag [value]))
    (rootOutside : OutLRange [(root.toNat,8,q.target)] q.source.toNat 8)
    (nonpointer : value.loc? = none) :
    (Eqv.val value id).P (reloc μ pl) q.target.toNat after :=
  post.payload_fixed object rootOutside (relocWord_fix _ nonpointer)

end OCaml.Vm.Gc.SingleField
