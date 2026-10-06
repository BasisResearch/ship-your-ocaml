import OCaml.Vm.Sim.ImmediateRows
import OCaml.Vm.Sim.AccRows
import OCaml.Vm.Sim.Offsetint
import OCaml.Vm.Sim.Constint
import OCaml.Vm.Sim.Branch
import OCaml.Vm.Sim.Atom
import OCaml.Vm.Sim.Branchif
import OCaml.Vm.Sim.Branchifnot
import OCaml.Vm.Sim.Beq
import OCaml.Vm.Sim.Bneq
import OCaml.Vm.Sim.Bltint
import OCaml.Vm.Sim.Bleint
import OCaml.Vm.Sim.Bgtint
import OCaml.Vm.Sim.Bgeint
import OCaml.Vm.Sim.Bultint
import OCaml.Vm.Sim.Bugeint

/-!
# Unconditional rows: arms with code operands

OFFSETINT, CONSTINT, BRANCH and the six immediate compare-and-branch
opcodes. Operand words come from their fetch (`OperandAt.of_fetch`, geometry
from the loop-head witness); the semantic inversions are the real `stepI`
cases.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **OFFSETINT from the loop head.** -/
theorem offsetint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .OFFSETINT)
    (fetch : P.code[s.pc + 1]? = some w) (step : stepI P s ⟨.OFFSETINT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change (match s.accu with
    | .int a => Res.next { (s.adv 2) with
        accu := .int (untag (tag64 a + ((BitVec.ofInt 32 w.toInt <<< 1).signExtend 64))) }
    | _ => .wrong) = .next s' at step
  split at step
  · rename_i n accu
    exact input_row h code fun input =>
      offsetint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) accu (by simp only [stepI, accu]; exact step)
  · cases step

/-- **CONSTINT from the loop head.** -/
theorem constint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONSTINT)
    (fetch : P.code[s.pc + 1]? = some w) (step : stepI P s ⟨.CONSTINT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  cases Res.next.inj step
  exact input_row h code fun input => constint_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch)

/-- **BRANCH from the loop head.** -/
theorem branch_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BRANCH)
    (fetch : P.code[s.pc + 1]? = some w) (step : stepI P s ⟨.BRANCH, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change opt (target s.pc 0 w.toInt) (fun t => Res.next { s with pc := t }) = .next s' at step
  obtain ⟨dest, jump, next⟩ := opt_next step
  cases Res.next.inj next
  exact input_row h code fun input => branch_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) jump

/-- **BLTINT from the loop head.** -/
theorem bltint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BLTINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BLTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bltint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BLEINT from the loop head.** -/
theorem bleint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BLEINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BLEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bleint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BGTINT from the loop head.** -/
theorem bgtint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BGTINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BGTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bgtint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BGEINT from the loop head.** -/
theorem bgeint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BGEINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BGEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bgeint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BULTINT from the loop head.** -/
theorem bultint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BULTINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BULTINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bultint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BUGEINT from the loop head.** -/
theorem bugeint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BUGEINT)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (step : stepI P s ⟨.BUGEINT, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bugeint_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **ATOM from the loop head.** The semantics makes a negative operand
`.unsupported` (it would index before `caml_atom_table`), so a successful
step supplies the arm's nonnegativity. -/
theorem atom_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ATOM)
    (fetch : P.code[s.pc + 1]? = some w) (step : stepI P s ⟨.ATOM, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  change (if w.toInt < 0 then Res.unsupported
    else Res.next { (s.adv 2) with accu := .atom w.toInt.toNat }) = .next s' at step
  split at step
  · cases step
  · rename_i nonneg
    cases Res.next.inj step
    exact input_row h code fun input => atom_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) (by omega)

/-- **BRANCHIF from the loop head.** `notRaw` is named: the semantics branches on
any non-zero accumulator, while the machine decides by the represented
word's parity (supplied by `ValuesInRange.accu_notRaw`). -/
theorem branchif_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BRANCHIF)
    (fetch : P.code[s.pc + 1]? = some w) (notRaw : ∀ x, s.accu ≠ .raw x)
    (step : stepI P s ⟨.BRANCHIF, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    branchif_arm stable input input.geometry.even notRaw (OperandAt.of_fetch input.geometry.toArmGeometry fetch) step

/-- **BRANCHIFNOT from the loop head.** `notRaw` is named: the semantics branches on
any non-zero accumulator, while the machine decides by the represented
word's parity (supplied by `ValuesInRange.accu_notRaw`). -/
theorem branchifnot_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BRANCHIFNOT)
    (fetch : P.code[s.pc + 1]? = some w) (notRaw : ∀ x, s.accu ≠ .raw x)
    (step : stepI P s ⟨.BRANCHIFNOT, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    branchifnot_arm stable input input.geometry.even notRaw (OperandAt.of_fetch input.geometry.toArmGeometry fetch) step

/-- **BEQ from the loop head**, for an integer accumulator. `integer` is
named: on a pointer the semantics falls through, while `interp.c` compares
the immediate with `Long_val` of the address, which can coincide
(`beq_pointer_guard_obstruction`). -/
theorem beq_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BEQ)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (integer : s.accu.isInt = true)
    (step : stepI P s ⟨.BEQ, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    beq_step_arm stable input integer (OperandAt.of_fetch input.geometry.toArmGeometry fetch)
      (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

/-- **BNEQ from the loop head**, for an integer accumulator. `integer` is
named: on a pointer the semantics falls through, while `interp.c` compares
the immediate with `Long_val` of the address, which can coincide
(`beq_pointer_guard_obstruction`). -/
theorem bneq_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {imm ofs : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BNEQ)
    (fetch : P.code[s.pc + 1]? = some imm) (fetchOfs : P.code[s.pc + 2]? = some ofs)
    (integer : s.accu.isInt = true)
    (step : stepI P s ⟨.BNEQ, [imm.toInt, ofs.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' :=
  input_row h code fun input =>
    bneq_step_arm stable input integer (OperandAt.of_fetch input.geometry.toArmGeometry fetch)
      (OperandAt.of_fetch input.geometry.toArmGeometry fetchOfs) step

theorem beq_no_halt {P : Prog} {s : St} {n o : Int} {e : Nat} {w : World} :
    stepI P s ⟨.BEQ, [n, o]⟩ ≠ .halt e w := by
  intro h; simp only [stepI, brOp, opt] at h; repeat' split at h
  all_goals cases h

theorem bneq_no_halt {P : Prog} {s : St} {n o : Int} {e : Nat} {w : World} :
    stepI P s ⟨.BNEQ, [n, o]⟩ ≠ .halt e w := by
  intro h; simp only [stepI, brOp, opt] at h; repeat' split at h
  all_goals cases h

end OCaml.Vm.Sim
