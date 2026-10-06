import OCaml.Vm.Sim.StackRows
import OCaml.Vm.Sim.ImmediateRows
import OCaml.Vm.Sim.Pushconst0
import OCaml.Vm.Sim.Pushconst1
import OCaml.Vm.Sim.Pushconst2
import OCaml.Vm.Sim.Pushconst3
import OCaml.Vm.Sim.Pushconstint
import OCaml.Vm.Sim.Pushatom0
import OCaml.Vm.Sim.Pushatom

/-!
# Unconditional rows: push a constant

PUSHCONST0–3, PUSHCONSTINT, PUSHATOM0 and PUSHATOM push the accumulator
and load a constant. `push_set_row` is `push_next` (`StackRows.lean`) with
the successor left to the arm: the write window from `RuntimeFrame`, the
push separation from `PushWriteOk.of_geometry`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **A push row** with any successor. -/
theorem push_set_row {L : OCaml.Layout} {P : Prog} {s t : St} {c : Config} {op : Opcode}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (arm : ∀ {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 64},
      WindowStable L.runtimeOk [⟨sp - 8, sp⟩] → ArmInput L P s op c pl cp sp high →
      PushWriteOk P s c pl cp sp w → valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P t c') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P t c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨w, -, pushed⟩ := input.accu
  obtain ⟨c', run, running⟩ := arm (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry.toArmGeometry input.stack space) pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- **PUSHCONST0 from the loop head.** -/
theorem pushconst0_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .PUSHCONST0)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHCONST0, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed => pushconst0_arm stable input write pushed

/-- **PUSHCONST1 from the loop head.** -/
theorem pushconst1_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .PUSHCONST1)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHCONST1, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed => pushconst1_arm stable input write pushed

/-- **PUSHCONST2 from the loop head.** -/
theorem pushconst2_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .PUSHCONST2)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHCONST2, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed => pushconst2_arm stable input write pushed

/-- **PUSHCONST3 from the loop head.** -/
theorem pushconst3_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .PUSHCONST3)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHCONST3, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed => pushconst3_arm stable input write pushed

/-- **PUSHATOM0 from the loop head.** -/
theorem pushatom0_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .PUSHATOM0)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHATOM0, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed => pushatom0_arm stable input write pushed

/-- **PUSHCONSTINT from the loop head.** -/
theorem pushconstint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    {w : BitVec 32} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHCONSTINT) (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHCONSTINT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact push_set_row rf h code space fun stable input write pushed =>
    pushconstint_arm stable input write (OperandAt.of_fetch input.geometry.toArmGeometry fetch) pushed

/-- **PUSHATOM from the loop head.** A negative operand is `.unsupported`. -/
theorem pushatom_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    {w : BitVec 32} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .PUSHATOM) (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : stepI P s ⟨.PUSHATOM, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
  cases Res.next.inj (Res.unguard step)
  exact push_set_row rf h code space fun stable input write pushed =>
    pushatom_arm stable input write (OperandAt.of_fetch input.geometry.toArmGeometry fetch) nonnegative pushed

end OCaml.Vm.Sim
