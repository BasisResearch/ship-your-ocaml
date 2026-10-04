import OCaml.Vm.Gc.ForwardingTable
import OCaml.Vm.Gc.SingleFieldForwardedReturn
import OCaml.Vm.Gc.SingleFieldFreshLarge

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives

/-- Exact child allocation grows the parent's partial forwarding table. -/
theorem ChildAllocated.table {q root sp before after copies pl}
    (post : ChildAllocated q root sp before after) (view : (ForwardingTable.eqv copies).P pl 0 before)
    (window : WriteWindow q.source 8)
    (outside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root))
    (allocationOutside : ForwardingTable.Outside (q :: copies)
      (AllocWrapper.effect (childAllocatorRegs q root sp before) (forwardedSnapshot q root before))) :
    (ForwardingTable.eqv (q :: copies)).P pl 0 after :=
  ForwardingTable.publish_then view post.memory window outside allocationOutside

/-- The least-large-block alternative supplies the same table extension. -/
theorem ChildLargeAllocated.table {q root sp before after copies pl}
    (post : ChildLargeAllocated q root sp before after) (view : (ForwardingTable.eqv copies).P pl 0 before)
    (window : WriteWindow q.source 8)
    (outside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root))
    (allocationOutside : ForwardingTable.Outside (q :: copies)
      (AllocLargeWrapper.effect (childAllocatorRegs q root sp before) (forwardedSnapshot q root before))) :
    (ForwardingTable.eqv (q :: copies)).P pl 0 after :=
  ForwardingTable.publish_then view post.memory window outside allocationOutside

/-- The table supplies the typed forwarding observation used by the actual
child return. It does not assume ScanCoherent or a represented post-state. -/
theorem ForwardedReturned.payload_from_table {q root sp before after pl cp tag copies entry l}
    (post : ForwardedReturned q root sp before after)
    (object : ObjAt before pl cp q.source.toNat (.block tag [.ptr l 0]))
    (rootOutside : OutLRange [(root.toNat,8,q.target)] q.source.toNat 8)
    (table : (ForwardingTable.eqv copies).P pl 0 (forwardedSnapshot q root before))
    (member : entry ∈ copies) (captured : child q root before = entry.source)
    (placed : pl.φ l = some entry.source.toNat) :
    (Reloc.Eqv.val (.ptr l 0) id).P (Reloc.reloc (ForwardingTable.relocation copies) pl) q.target.toNat after := by
  apply post.payload object rootOutside
  simpa only [forwardedValue,captured] using ForwardingTable.pointer_action table member placed

end OCaml.Vm.Gc.SingleField
