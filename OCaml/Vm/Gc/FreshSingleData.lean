import OCaml.Vm.Gc.FreshSingle

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives

/-- The captured child is the original field when allocation and the root
store preserve that field. Both premises are finite memory footprints. -/
theorem single_child_original {R target log c}
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8) :
    SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c) = word c (R 10).toNat := by
  rw [SingleField.child_original rootOutside]
  simp only [queuePending,queueSnapshot,word,bytesT_writeLog_out _ allocationOutside]

/-- The complete single-field route establishes the represented payload.
There are no deferred suffix fields for mopup to copy. -/
theorem SingleResult.payload {R target log before after pl cp tag value}
    (post : SingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8) :
    (pendingPayload (queuePending R target) [value]).P pl target.toNat after := by
  have first := post.value.trans (single_child_original allocationOutside rootOutside)
  apply pendingPayload_of_observations (q := queuePending R target) object first
  intro i v hi nonzero
  cases i with
  | zero => exact False.elim (nonzero rfl)
  | succ i => simp at hi

end OCaml.Vm.Gc.Fresh
