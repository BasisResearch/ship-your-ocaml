import OCaml.Vm.Sim.CcallNames
import OCaml.Programs.WhileMinShape
import OCaml.Vm.Gc.F1Runtime

/-!
# `whileMin`'s C_CALL returns from its seven primitives

Every reached `C_CALLk` site of `while_min.byte` names one of `whileMinCalls op`
(checked in the one shape run, `St.callNamesOk`). So its `CcallReturns` is
assembled from those primitives' summaries alone (`CcallReturns.of_names`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives OCaml.Programs

/-- At a `CcallReady` site of a reachable `whileMin` state, the named primitive
is one of `whileMinCalls op`. -/
theorem whileMin_call_named {op : Opcode}
    (hop : op = .C_CALL1 ∨ op = .C_CALL2 ∨ op = .C_CALL3 ∨ op = .C_CALL4 ∨ op = .C_CALL5)
    {s : St} {c : Config} {pl : Place} {cp : ChanPlace} {sp high domain table entry : Nat}
    {value env : BitVec 64} {index : BitVec 32} {name : String} (reach : Reach whileMin s)
    (ready : CcallReady op Gc.f1Layout whileMin s c pl cp sp high domain table entry value env index name) :
    name ∈ whileMinCalls op := by
  have shape := whileMin_shapeOk reach
  obtain ⟨i, hd, -⟩ := shape.decode
  have fetch := (decode_fetch hd).1.fetch
  have at_ : s.atOp whileMin op := fetch.trans (congrArg some (ready.toArmInput.fetch fetch))
  have names := shape.callNames
  have operand := ready.operand.fetch
  have prim := ready.primitive
  have one : St.namesOk whileMin (whileMinCalls op) op s = true := by
    simp only [St.callNamesOk, Bool.and_eq_true] at names
    rcases hop with rfl | rfl | rfl | rfl | rfl
    · exact names.1.1.1.1
    · exact names.1.1.1.2
    · exact names.1.1.2
    · exact names.1.2
    · exact names.2
  simp only [St.namesOk, if_pos at_, operand, prim, List.contains_iff_mem] at one
  exact one

/-- **`whileMin`'s C_CALL returns** from summaries of its seven primitives. -/
theorem whileMin_ccallReturns {op : Opcode} {ra : BitVec 64} {k : Nat}
    (hop : op = .C_CALL1 ∨ op = .C_CALL2 ∨ op = .C_CALL3 ∨ op = .C_CALL4 ∨ op = .C_CALL5)
    (each : ∀ name ∈ whileMinCalls op, PrimReturnsAt Gc.f1Layout whileMin op ra k name) :
    CcallReturns Gc.f1Layout whileMin op ra k :=
  .of_names each fun _ _ _ _ _ _ _ _ _ _ _ _ reach ready _ => whileMin_call_named hop reach ready

end OCaml.Vm.Sim
