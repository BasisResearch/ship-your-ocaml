import OCaml.Programs.WhileMin
import OCaml.Bytecode.GcSafeNoForward
import OCaml.Run.Checked
import OCaml.Vm.Gc.G1Room

/-!
# `Fits` and `GcSafe` for `whileMin`, kernel-checked

One `decide +kernel` of `Run.checkAll` walks the 2,161-step run once and checks
at every state: stack at most 18 words, heap at most 125 words (100 of them
the initial heap), and no `Forward_tag` block. `whileMin` never forces a lazy
value, so it is GC-safe (`gcSafe_of_noForward`), and it fits the F1 budget.
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

namespace OCaml.Programs
open OCaml.Bytecode

/-- The measured peak resources of `whileMin`'s run. -/
def whileMinPeak : Budget := ⟨18, 125⟩

/-- The per-state check: within the peak budget and free of `Forward_tag` blocks. -/
def whileMinOk (s : St) : Bool :=
  decide (s.stack.length ≤ whileMinPeak.stackWords ∧ s.heap.words ≤ whileMinPeak.heapWords) &&
    s.heap.noForward

set_option maxRecDepth 100000 in
theorem whileMin_checked : Run.checkAll (bcK whileMin) whileMinOk 2200 whileMin.init = true := by
  decide +kernel

theorem whileMin_ok {s : St} (reach : Reach whileMin s) :
    (s.stack.length ≤ whileMinPeak.stackWords ∧ s.heap.words ≤ whileMinPeak.heapWords) ∧
      s.heap.noForward = true := by
  have h := reach_of_checkAll whileMin_checked reach
  simp only [whileMinOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- `whileMin` stays within its measured peak. -/
theorem whileMin_fitsPeak : Fits whileMinPeak whileMin := fun _ reach => (whileMin_ok reach).1

/-- **`Fits g1Budget whileMin`**: within the F1 budget. -/
theorem whileMin_fits : Fits Vm.Gc.g1Budget whileMin :=
  whileMin_fitsPeak.mono (by decide) (by decide)

/-- `whileMin` never creates a `Forward_tag` block. -/
theorem whileMin_noForward : NoForward whileMin := fun _ reach => (whileMin_ok reach).2

/-- **`GcSafe whileMin`**. -/
theorem whileMin_gcSafe : GcSafe whileMin := gcSafe_of_noForward whileMin_noForward

end OCaml.Programs
