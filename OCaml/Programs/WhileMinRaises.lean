import OCaml.Programs.WhileMinChecks
import OCaml.Bytecode.PtrOffsets
import OCaml.Vm.Sim.RaiseRows

/-!
# `RaisesCaught whileMin`, kernel-checked

Every reachable raise opcode finds a trap frame (`s.trap ≠ 0`), by one
`decide +kernel` of `Run.checkAll` over the run.
-/

namespace OCaml.Vm.Sim
open OCaml.Bytecode

/-- The per-state check: at a raise opcode, a trap frame is installed. -/
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

end OCaml.Vm.Sim

namespace OCaml.Programs
open OCaml.Bytecode OCaml.Vm.Sim

set_option maxRecDepth 100000 in
theorem whileMin_raisesChecked :
    Run.checkAll (bcK whileMin) (St.raisesOk whileMin) 2200 whileMin.init = true := by
  decide +kernel

/-- **Every reachable raise in `whileMin` is caught.** -/
theorem whileMin_raisesCaught : RaisesCaught whileMin :=
  .of_check fun _ reach => reach_of_checkAll whileMin_raisesChecked reach

end OCaml.Programs
