import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.ExtraBound

/-!
# `ExtraBounded whileMin`, kernel-checked

One `decide +kernel` of `Run.checkAll` over the 2,161-step run.
-/

namespace OCaml.Programs
open OCaml.Bytecode

set_option maxRecDepth 100000 in
theorem whileMin_extraChecked :
    Run.checkAll (bcK whileMin) St.extraOk 2200 whileMin.init = true := by
  decide +kernel

/-- **`whileMin`'s extra-argument counts are bounded.** -/
theorem whileMin_extraBounded : ExtraBounded whileMin :=
  .of_check fun _ reach => reach_of_checkAll whileMin_extraChecked reach

end OCaml.Programs
