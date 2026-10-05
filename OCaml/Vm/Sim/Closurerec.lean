import OCaml.Vm.Sim.ClosurerecMachine
import OCaml.Vm.Sim.ClosurerecModel

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Complete represented CLOSUREREC nursery arm: actual dispatch, allocation,
capture and infix loops, return, and full data/platform restoration. -/
theorem closurerec_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest a domain limit : Nat}
    {functions count firstOffset : BitVec 32} {accu : BitVec 64} {targets : List Nat} {offsets : Nat → BitVec 32}
    (h : ArmInput L P s .CLOSUREREC c pl cp sp high)
    (functionsOperand : OperandAt P pl (s.pc + 1) functions) (functionsPositive : 0 < functions.toInt)
    (countOperand : OperandAt P pl (s.pc + 2) count) (nonnegative : 0 ≤ count.toInt)
    (firstOperand : OperandAt P pl (s.pc + 3) firstOffset) (jump : target s.pc 2 firstOffset.toInt = some dest)
    (arity : functions.toInt.toNat = targets.length + 1) (value : valWord pl s.accu = some accu)
    (runtime : AllocationRuntime L.runtimeOk c (closurerecFullLog c pl sp count.toInt.toNat dest a domain accu targets))
    (writes : ClosurerecWriteOk P s c pl cp sp count.toInt.toNat dest a domain accu targets)
    (apart : OutWRange [stackWindow high] (a - 8)
      (8 * (closurerecObject s count.toInt.toNat (dest :: targets)).wosize + 8))
    (arenaEnd : a + 8 * (closurerecObject s count.toInt.toNat (dest :: targets)).wosize ≤
      Vsa.Sim.DlHeap.heapEnd)
    (arena : LogInW [arenaWindow] (closurerecFullLog c pl sp count.toInt.toNat dest a domain accu targets))
    (space : ClosurerecMachineInput c pl s.pc sp count.toInt.toNat dest a domain limit accu targets offsets) :
    ∃ after, Plus c after ∧ Running L P (closurerecState s count.toInt.toNat dest targets) after := by
  obtain ⟨after, run, post⟩ := closurerec_machine h functionsOperand functionsPositive countOperand nonnegative
    firstOperand jump arity value space
  exact ⟨after, run, closurerec_restore runtime h.toVmReprAt h.running.platform h.dispatch.loop value writes post
    h.geometry apart arenaEnd arena h.native⟩

/-- The represented constructor agrees with the successful bytecode step. -/
theorem closurerec_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest a domain limit : Nat}
    {functions count firstOffset : BitVec 32} {accu : BitVec 64} {targets : List Nat} {offsets : Nat → BitVec 32}
    (modelOffsets : List Int)
    (offsetCount : modelOffsets.length = functions.toInt.toNat)
    (jumps : modelOffsets.mapM (fun o => target s.pc 2 o) = some (dest :: targets))
    (step : stepI P s ⟨.CLOSUREREC, functions.toInt :: count.toInt :: modelOffsets⟩ = .next s')
    (h : ArmInput L P s .CLOSUREREC c pl cp sp high)
    (functionsOperand : OperandAt P pl (s.pc + 1) functions) (functionsPositive : 0 < functions.toInt)
    (countOperand : OperandAt P pl (s.pc + 2) count) (nonnegative : 0 ≤ count.toInt)
    (firstOperand : OperandAt P pl (s.pc + 3) firstOffset) (jump : target s.pc 2 firstOffset.toInt = some dest)
    (arity : functions.toInt.toNat = targets.length + 1) (value : valWord pl s.accu = some accu)
    (runtime : AllocationRuntime L.runtimeOk c (closurerecFullLog c pl sp count.toInt.toNat dest a domain accu targets))
    (writes : ClosurerecWriteOk P s c pl cp sp count.toInt.toNat dest a domain accu targets)
    (apart : OutWRange [stackWindow high] (a - 8)
      (8 * (closurerecObject s count.toInt.toNat (dest :: targets)).wosize + 8))
    (arenaEnd : a + 8 * (closurerecObject s count.toInt.toNat (dest :: targets)).wosize ≤
      Vsa.Sim.DlHeap.heapEnd)
    (arena : LogInW [arenaWindow] (closurerecFullLog c pl sp count.toInt.toNat dest a domain accu targets))
    (space : ClosurerecMachineInput c pl s.pc sp count.toInt.toNat dest a domain limit accu targets offsets) :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state := closurerec_state_of_step arity offsetCount writes.bound jumps step
  rw [← state]
  exact closurerec_arm h functionsOperand functionsPositive countOperand nonnegative firstOperand jump arity value runtime writes apart arenaEnd arena space

end OCaml.Vm.Sim
