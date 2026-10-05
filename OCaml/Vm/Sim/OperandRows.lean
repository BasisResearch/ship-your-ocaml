import OCaml.Vm.Sim.CodeFacts
import OCaml.Vm.Sim.ImmediateRows
import OCaml.Vm.Sim.AccRows
import OCaml.Vm.Sim.Offsetint
import OCaml.Vm.Sim.Constint
import OCaml.Vm.Sim.Branch
import OCaml.Vm.Sim.Atom
import OCaml.Vm.Sim.Bltint
import OCaml.Vm.Sim.Bleint
import OCaml.Vm.Sim.Bgtint
import OCaml.Vm.Sim.Bgeint
import OCaml.Vm.Sim.Bultint
import OCaml.Vm.Sim.Bugeint

/-!
# Unconditional rows: arms with code operands

OFFSETINT, CONSTINT, BRANCH and the six immediate compare-and-branch
opcodes. Operand words come through `OperandCode` (`CodeFacts.lean`); the
semantic inversions are the real `stepI` cases.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **OFFSETINT from the loop head.** -/
theorem offsetint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .OFFSETINT)
    (operand : OperandCode P s c 1 w) (step : stepI P s ⟨.OFFSETINT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  change (match s.accu with
    | .int a => Res.next { (s.adv 2) with
        accu := .int (untag (tag64 a + ((BitVec.ofInt 32 w.toInt <<< 1).signExtend 64))) }
    | _ => .wrong) = .next s' at step
  split at step
  · rename_i n accu
    exact input_row h code fun input =>
      offsetint_step_arm stable input (operand.of_input input) accu (by simp only [stepI, accu]; exact step)
  · cases step

/-- **CONSTINT from the loop head.** -/
theorem constint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONSTINT)
    (operand : OperandCode P s c 1 w) (step : stepI P s ⟨.CONSTINT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step
  exact input_row h code fun input => constint_arm stable input (operand.of_input input)

/-- **BRANCH from the loop head.** -/
theorem branch_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BRANCH)
    (operand : OperandCode P s c 1 w) (step : stepI P s ⟨.BRANCH, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  change opt (target s.pc 0 w.toInt) (fun t => Res.next { s with pc := t }) = .next s' at step
  obtain ⟨dest, jump, next⟩ := opt_next step
  cases Res.next.inj next
  exact input_row h code fun input => branch_arm stable input (operand.of_input input) jump

/-- **BLTINT from the loop head.** -/
theorem bltint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BLTINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BLTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bltint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **BLEINT from the loop head.** -/
theorem bleint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BLEINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BLEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bleint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **BGTINT from the loop head.** -/
theorem bgtint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BGTINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BGTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bgtint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **BGEINT from the loop head.** -/
theorem bgeint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BGEINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BGEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bgeint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **BULTINT from the loop head.** -/
theorem bultint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BULTINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BULTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bultint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **BUGEINT from the loop head.** -/
theorem bugeint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BUGEINT)
    (operand : OperandCode P s c 1 imm) (offset : OperandCode P s c 2 ofs)
    (step : stepI P s ⟨.BUGEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  input_row h code fun input =>
    bugeint_step_arm stable input (operand.of_input input) (offset.of_input input) step

/-- **ATOM from the loop head.** The semantics makes a negative operand
`.unsupported` (it would index before `caml_atom_table`), so a successful
step supplies the arm's nonnegativity. -/
theorem atom_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ATOM)
    (operand : OperandCode P s c 1 w) (step : stepI P s ⟨.ATOM, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  change (if w.toInt < 0 then Res.unsupported
    else Res.next { (s.adv 2) with accu := .atom w.toInt.toNat }) = .next s' at step
  split at step
  · cases step
  · rename_i nonneg
    cases Res.next.inj step
    exact input_row h code fun input => atom_arm stable input (operand.of_input input) (by omega)

end OCaml.Vm.Sim
