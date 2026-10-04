import OCaml.Vm.Sim.DivintCall
import OCaml.Vm.Sim.ModintCall
import OCaml.Run.Machine
import Vsa.Sim.DeriveCallSeg

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Select the generated caller prefix for the requested signed operation. -/
theorem division_setup (kind : DivisionKind) {L : OCaml.Layout} {P : Prog} {s : St} {c d : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {x y : BitVec 63} {rest : List Val}
    (h : ArmInput L P s (divisionOpcode kind) c pl cp sp high)
    (accu : s.accu = .int x) (stack : s.stack = .int y :: rest) (nonzero : y ≠ 0)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8) (scratch : BinaryLibScratch c)
    (dp : DispatchPost c (divisionOpcode kind) (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d) :
    ∃ n after, StepsN n d after ∧ DivisionCall kind d pl (s.pc + 1) sp x y after := by
  cases kind with
  | quotient => exact divint_setup h accu stack nonzero read scratch dp
  | remainder => exact modint_setup h accu stack nonzero read scratch dp

/-- Select the generated retagging and stack-consuming suffix. -/
theorem division_return (kind : DivisionKind) {before : Config} {pl : Place} {pc sp : Nat} {x y : BitVec 63} :
    Vsa.Logic.Triple (DivisionReturn kind before pl pc sp x y)
      (ConsumePost before pl pc (sp + 8) (divisionResult kind x y)) := by
  cases kind with
  | quotient => exact divint_return
  | remainder => exact modint_return

/-- Complete represented DIVINT/MODINT arms for nonzero VM divisors.
Both use the proved signed libgcc call and the shared consuming restoration. -/
theorem division_arm (kind : DivisionKind) {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {x y : BitVec 63} {rest : List Val}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s (divisionOpcode kind) c pl cp sp high)
    (accu : s.accu = .int x) (stack : s.stack = .int y :: rest) (nonzero : y ≠ 0)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8) (scratch : BinaryLibScratch c) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := s.pc + 1, accu := .int (divisionResult kind x y), stack := rest} after := by
  have bound : 1 ≤ s.stack.length := by simp only [stack, List.length_cons]; omega
  have restore := consume_arm (pc := s.pc + 1) (count := 1) (n := divisionResult kind x y) stable h bound
  simp only [stack, List.drop_succ_cons, List.drop_zero, Nat.mul_one] at restore
  apply restore
  intro d dp
  obtain ⟨n, call, run, post⟩ := division_setup kind h accu stack nonzero read scratch dp
  have start : Vsa.Logic.Triple (fun e => e = d) (DivisionCall kind d pl (s.pc + 1) sp x y) := by
    rintro e rfl
    exact ⟨call, run.toSteps, post⟩
  obtain ⟨after, run, post⟩ := (callSeg start division_callee (division_return kind)) d rfl
  exact ⟨_, after, run.toN_of_stepsField, post⟩

/-- The native nonzero signed operation agrees with the actual bytecode step. -/
theorem division_step_arm (kind : DivisionKind) {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {x y : BitVec 63} {rest : List Val}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s (divisionOpcode kind) c pl cp sp high)
    (accu : s.accu = .int x) (stack : s.stack = .int y :: rest) (nonzero : y ≠ 0)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8) (scratch : BinaryLibScratch c)
    (step : stepI P s ⟨divisionOpcode kind, []⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have nonzeroWord : y ≠ 0#63 := nonzero
  have state : {s with pc := s.pc + 1, accu := .int (divisionResult kind x y), stack := rest} = s' := by
    cases kind <;> simpa [stepI, divisionOpcode, divisionResult, accu, stack, ints?, opt, nonzeroWord, St.adv] using step
  rw [← state]
  exact division_arm kind stable h accu stack nonzero read scratch

end OCaml.Vm.Sim
