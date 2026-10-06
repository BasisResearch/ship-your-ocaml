import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets

/-!
# `ValuesInRange whileMin`, kernel-checked

One `decide +kernel` of `Run.checkAll` over the 2,161-step run checks that
every accumulator and stack value lies in its region.
-/

namespace OCaml.Programs
open OCaml.Bytecode

set_option maxRecDepth 100000 in
theorem whileMin_valuesChecked :
    Run.checkAll (bcK whileMin) (St.valuesInRange whileMin.code.size) 2200 whileMin.init = true := by
  decide +kernel

/-- **`whileMin`'s live values lie in their regions.** -/
theorem whileMin_valuesInRange : ValuesInRange whileMin := fun _ reach =>
  reach_of_checkAll whileMin_valuesChecked reach

set_option maxRecDepth 100000 in
theorem whileMin_branchChecked :
    Run.checkAll (bcK whileMin) (St.branchIntsOk whileMin) 2200 whileMin.init = true := by
  decide +kernel

/-- **`whileMin`'s immediate branches see integers.** -/
theorem whileMin_branchInts : BranchInts whileMin :=
  .of_check fun _ reach => reach_of_checkAll whileMin_branchChecked reach

end OCaml.Programs
