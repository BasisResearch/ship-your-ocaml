import OCaml.Vm.Gc.ChainPlan

namespace OCaml.Vm.Gc
open Vsa.Sim Primitives

/-- Concatenate finite access certificates at their reflected state. This
shares optional-path composition without duplicating the machine run proof. -/
theorem ChainAccess.append_eval {mem : Std.ExtHashMap Nat (BitVec 8)}
    {state : SegEvalState} {left right : List BBlock}
    (first : ChainAccess (writeLog mem state.log) state.regs state.loads left)
    (second : ChainAccess (writeLog mem (evalBlocks left state).log)
      (evalBlocks left state).regs (evalBlocks left state).loads right) :
    ChainAccess (writeLog mem state.log) state.regs state.loads (left ++ right) := by
  induction left generalizing state with
  | nil => exact second
  | cons block rest ih =>
    cases first with
    | cons head tail =>
      apply ChainAccess.cons head
      have composed := ih (state := evalBlock state block) (by
        simpa only [evalBlock,writeLog_append] using tail) second
      simpa only [evalBlock,writeLog_append,List.append_eq] using composed

end OCaml.Vm.Gc
