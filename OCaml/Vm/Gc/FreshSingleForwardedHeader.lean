import OCaml.Vm.Gc.FreshSingleForwarded
import OCaml.Vm.Gc.FreshHeaderCore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- Child forwarding and the native return preserve the allocator's typed
header. The concrete allocation header lemmas supply the initial premise. -/
theorem ForwardedSingleResult.header {R target log before after size tag a}
    (post : ForwardedSingleResult R target log before after)
    (header : HeaderOk (word (queueSnapshot R log before) a) size tag)
    (outside : OutLRange (SingleField.forwardedEffect (queuePending R target) (R 11)
      (queueSnapshot R log before)) a 8) : HeaderOk (word after a) size tag := by
  apply header_of_suffix ?_ header outside
  simp only [queueSnapshot,post.memory,writeLog_append]

/-- Whole allocation/forwarding/return result as an object under the new
placement. Header preservation and the typed child action are independent:
the allocation's color bits need not match the old nursery header. -/
theorem ForwardedSingleResult.object {R target log before after pl cp tag value μ}
    (post : ForwardedSingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (forwarding : SingleField.forwardedValue (queuePending R target) (R 11) (queueSnapshot R log before) =
      Reloc.relocWord μ pl value (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before)))
    (header : HeaderOk (word (queueSnapshot R log before) (target.toNat - Layout.header_bytes)) 1 tag)
    (headerOutside : OutLRange (SingleField.forwardedEffect (queuePending R target) (R 11)
      (queueSnapshot R log before)) (target.toNat - Layout.header_bytes) 8) :
    ObjAt after (Reloc.reloc μ pl) cp target.toNat (.block tag [value]) := by
  refine ⟨post.header header headerOutside,?_⟩
  have payload := post.payload object allocationOutside rootOutside forwarding
  intro i v hi
  cases i with
  | zero =>
    have equal : value = v := Option.some.inj hi
    subst v
    simpa [Reloc.Eqv.val] using payload
  | succ i => simp at hi

end OCaml.Vm.Gc.Fresh
