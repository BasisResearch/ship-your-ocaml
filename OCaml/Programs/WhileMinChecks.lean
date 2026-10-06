import OCaml.Programs.WhileMin
import OCaml.Bytecode.GcSafeNoForward
import OCaml.Run.Checked
import OCaml.Vm.Gc.G1Room
import OCaml.Refinement

/-!
# Checked runs: every-state facts from one kernel evaluation

`reach_of_checkAll` turns one `Run.checkAll` evaluation into a fact at every
reachable state. For `whileMin` there is exactly ONE such run,
`WhileMinShape.whileMin_shapeChecked` (`St.shapeOk`); its `Fits`, `NoForward`
and `GcSafe` corollaries live there. Never add a second `decide +kernel` over
the run: extend `St.shapeOk`.
-/

namespace OCaml.Bytecode

/-- A successful `checkAll` from `P.init` holds at every reachable state. -/
theorem reach_of_checkAll {P : Prog} {ok : St → Bool} {fuel : Nat}
    (h : Run.checkAll (bcK P) ok fuel P.init = true) {s : St} (reach : Reach P s) : ok s = true := by
  obtain ⟨n, run⟩ := reach
  exact Run.checkAll_reach h (stepsN_iff.1 run)

/-- `Fits` is monotone in the budget. -/
theorem _root_.OCaml.Fits.mono {B B' : Budget} {P : Prog} (h : Fits B P)
    (stack : B.stackWords ≤ B'.stackWords) (heap : B.heapWords ≤ B'.heapWords) : Fits B' P :=
  fun s reach => ⟨Nat.le_trans (h s reach).1 stack, Nat.le_trans (h s reach).2 heap⟩

end OCaml.Bytecode


