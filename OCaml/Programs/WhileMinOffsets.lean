import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets

/-!
# `PtrsInBlock whileMin`, kernel-checked

One `decide +kernel` of `Run.checkAll` over the 2,161-step run checks that
every accumulator and stack pointer stays within its block.
-/

namespace OCaml.Programs
open OCaml.Bytecode

set_option maxRecDepth 100000 in
theorem whileMin_ptrsChecked :
    Run.checkAll (bcK whileMin) St.ptrsInBlock 2200 whileMin.init = true := by
  decide +kernel

/-- **`whileMin`'s pointers stay within their blocks.** -/
theorem whileMin_ptrsInBlock : PtrsInBlock whileMin := fun _ reach =>
  reach_of_checkAll whileMin_ptrsChecked reach

end OCaml.Programs
