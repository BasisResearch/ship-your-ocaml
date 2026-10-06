import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets
import OCaml.Bytecode.ExtraBound
import OCaml.Bytecode.TrapBound
import OCaml.Vm.Sim.RaiseRows

/-!
# The F1 shape facts of `whileMin`, kernel-checked by one run

One `decide +kernel` of `Run.checkAll` over the 2,161-step run checks, at
every state, the per-program reachability facts the F1 arms name: live values
in their regions (`ValuesInRange`), small extra counts (`ExtraBounded`), the
trap pointer inside the stack (`TrapBounded`), immediate branches on integers
(`BranchInts`) and caught raises (`RaisesCaught`). One combined run, not one
per fact: each run of the kernel costs several GB.
-/

namespace OCaml.Vm.Sim
open OCaml.Bytecode

/-- The per-state raise check: at a raise opcode, a trap frame is installed. -/
def St.raisesOk (P : Prog) (s : St) : Bool :=
  if s.atOp P .RAISE ∨ s.atOp P .RERAISE ∨ s.atOp P .RAISE_NOTRACE then s.trap != 0 else true

theorem RaisesCaught.of_check {P : Prog} (h : ∀ s, Reach P s → St.raisesOk P s = true) :
    RaisesCaught P where
  caught s op reach member code := by
    have ok := h s reach
    have at_ : s.atOp P .RAISE ∨ s.atOp P .RERAISE ∨ s.atOp P .RAISE_NOTRACE := by
      simp only [raiseOps, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact .inl code.fetch
      · exact .inr (.inl code.fetch)
      · exact .inr (.inr code.fetch)
    simp only [St.raisesOk, if_pos at_, bne_iff_ne, ne_eq] at ok
    exact ok

/-- All F1 shape checks at one state. -/
def St.shapeOk (P : Prog) (s : St) : Bool :=
  s.valuesInRange P.code.size && s.extraOk && s.trapOk && s.branchIntsOk P && St.raisesOk P s

end OCaml.Vm.Sim

namespace OCaml.Programs
open OCaml.Bytecode OCaml.Vm.Sim

set_option maxRecDepth 100000 in
theorem whileMin_shapeChecked :
    Run.checkAll (bcK whileMin) (St.shapeOk whileMin) 2200 whileMin.init = true := by
  decide +kernel

theorem whileMin_shapeOk {s : St} (reach : Reach whileMin s) :
    s.valuesInRange whileMin.code.size = true ∧ s.extraOk = true ∧ s.trapOk = true ∧
      s.branchIntsOk whileMin = true ∧ St.raisesOk whileMin s = true := by
  have h := reach_of_checkAll whileMin_shapeChecked reach
  simp only [St.shapeOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- **`whileMin`'s live values lie in their regions.** -/
theorem whileMin_valuesInRange : ValuesInRange whileMin := fun _ reach => (whileMin_shapeOk reach).1

/-- **`whileMin`'s extra-argument counts are bounded.** -/
theorem whileMin_extraBounded : ExtraBounded whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).2.1

/-- **`whileMin`'s trap pointer stays inside the stack.** -/
theorem whileMin_trapBounded : TrapBounded whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).2.2.1

/-- **`whileMin`'s immediate branches see integers.** -/
theorem whileMin_branchInts : BranchInts whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).2.2.2.1

/-- **Every reachable raise in `whileMin` is caught.** -/
theorem whileMin_raisesCaught : RaisesCaught whileMin :=
  .of_check fun _ reach => (whileMin_shapeOk reach).2.2.2.2

end OCaml.Programs
