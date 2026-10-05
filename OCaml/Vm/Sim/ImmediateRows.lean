import OCaml.Vm.Sim.InvariantUse
import OCaml.Vm.Sim.Const0
import OCaml.Vm.Sim.Const1
import OCaml.Vm.Sim.Const2
import OCaml.Vm.Sim.Const3
import OCaml.Vm.Sim.Atom0
import OCaml.Vm.Sim.Negint
import OCaml.Vm.Sim.Boolnot

/-!
# Unconditional rows: immediate accumulator arms

CONST0–CONST3, ATOM0, NEGINT and BOOLNOT. Their conditional bridges state
the successor explicitly; each row inverts the real `stepI` (definitionally,
and for NEGINT/BOOLNOT by the accumulator case split the semantics itself
makes) and derives `ArmInput` from the loop head (`ArmInput.of_loop`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **An `ArmInput`-only row.** -/
theorem input_row {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (arm : ∀ {pl : Place} {cp : ChanPlace} {sp high : Nat}, ArmInput L P s op c pl cp sp high →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' :=
  let ⟨_, _, _, _, input⟩ := ArmInput.of_loop h code; arm input

/-- **CONST0 from the loop head.** -/
theorem const0_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONST0)
    (step : stepI P s ⟨.CONST0, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step; exact input_row h code fun input => const0_arm stable input

/-- **CONST1 from the loop head.** -/
theorem const1_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONST1)
    (step : stepI P s ⟨.CONST1, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step; exact input_row h code fun input => const1_arm stable input

/-- **CONST2 from the loop head.** -/
theorem const2_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONST2)
    (step : stepI P s ⟨.CONST2, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step; exact input_row h code fun input => const2_arm stable input

/-- **CONST3 from the loop head.** -/
theorem const3_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .CONST3)
    (step : stepI P s ⟨.CONST3, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step; exact input_row h code fun input => const3_arm stable input

/-- **ATOM0 from the loop head.** -/
theorem atom0_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .ATOM0)
    (step : stepI P s ⟨.ATOM0, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  cases Res.next.inj step; exact input_row h code fun input => atom0_arm stable input

/-- **NEGINT from the loop head.** -/
theorem negint_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .NEGINT)
    (step : stepI P s ⟨.NEGINT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  change (match s.accu with
    | .int a => Res.next { (s.adv 1) with accu := .int (untag (2 - tag64 a)) }
    | _ => .wrong) = .next s' at step
  split at step
  · rename_i n accu; cases Res.next.inj step
    exact input_row h code fun input => negint_arm stable input accu
  · cases step

/-- **BOOLNOT from the loop head.** -/
theorem boolnot_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .BOOLNOT)
    (step : stepI P s ⟨.BOOLNOT, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' := by
  change (match s.accu with
    | .int n => Res.next { (s.adv 1) with accu := .int (1 - n) }
    | _ => .wrong) = .next s' at step
  split at step
  · rename_i n accu; cases Res.next.inj step
    exact input_row h code fun input => boolnot_arm stable input accu
  · cases step

end OCaml.Vm.Sim
