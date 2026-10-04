import OCaml.Run.Positive
import OCaml.Vm.Sim.ClosurerecSetup
import OCaml.Vm.Sim.ClosurerecFirstOne
import OCaml.Vm.Sim.ClosurerecFirstMore
import OCaml.Vm.Sim.ClosurerecStack
import OCaml.Vm.Sim.ClosurerecReturn

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Concrete memory inputs for the full native recursive-closure nursery constructor. -/
structure ClosurerecMachineInput (c : Config) (pl : Place) (pc sp count dest a domain limit : Nat)
    (accu : BitVec 64) (targets : List Nat) (offsets : Nat → BitVec 32) : Prop where
  setup : ClosurerecSetupInput sp (targets.length + 1) count a domain limit accu c
  first : ClosurerecFirstInput c pl pc sp (targets.length + 1) count dest a domain accu
  infixLoop : InfixRegion pl pc a (closurerecStackStart sp count) targets offsets c
  prefixOutside : ∀ i, i < targets.length → OutLRange
    (closurerecReadyLog c sp (targets.length + 1) count a domain accu ++
      closurerecFirstLog pl sp (targets.length + 1) count dest a)
      (pl.codeBase + 4 * (pc + 4 + i)) 4

/-- The complete actual nursery path returns from CLOSUREREC with exact memory,
registers and frame. Represented object/stack restoration is a separate proof. -/
theorem closurerec_machine {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest a domain limit : Nat}
    {functions count firstOffset : BitVec 32} {accu : BitVec 64} {targets : List Nat} {offsets : Nat → BitVec 32}
    (h : ArmInput L P s .CLOSUREREC c pl cp sp high)
    (functionsOperand : OperandAt P pl (s.pc + 1) functions) (functionsPositive : 0 < functions.toInt)
    (countOperand : OperandAt P pl (s.pc + 2) count) (nonnegative : 0 ≤ count.toInt)
    (firstOperand : OperandAt P pl (s.pc + 3) firstOffset) (jump : target s.pc 2 firstOffset.toInt = some dest)
    (arity : functions.toInt.toNat = targets.length + 1) (value : valWord pl s.accu = some accu)
    (space : ClosurerecMachineInput c pl s.pc sp count.toInt.toNat dest a domain limit accu targets offsets) :
    ∃ after, Plus c after ∧ ClosurerecReturned c pl s.pc sp count.toInt.toNat dest a domain accu targets after := by
  have setup : ClosurerecSetupInput sp functions.toInt.toNat count.toInt.toNat a domain limit accu c := by
    rw [arity]; exact space.setup
  obtain ⟨ready, setupSteps, front⟩ := closurerec_setup h functionsOperand functionsPositive countOperand nonnegative value setup
  rw [arity] at front
  have firstRun : ∃ n middle, StepsN n ready middle ∧
      ClosurerecFirst c pl s.pc sp (targets.length + 1) count.toInt.toNat dest a domain accu middle := by
    by_cases more : 0 < targets.length
    · exact closurerec_first_more h firstOperand jump space.first (by omega) front
    · exact closurerec_first_one h firstOperand jump space.first (by omega) front
  obtain ⟨nf, first, firstSteps, firstPost⟩ := firstRun
  have doneRun : ∃ done, Steps first done ∧ ClosurerecDone c pl s.pc sp count.toInt.toNat dest a domain accu targets done := by
    by_cases more : 0 < targets.length
    · have region := space.infixLoop.frame firstPost.memory space.prefixOutside
      obtain ⟨copied, copiedSteps, back⟩ := infix_run region first (firstPost.infix_start more)
      obtain ⟨ns, done, stackSteps, post⟩ := closurerec_stack firstPost back region.room
      exact ⟨done, copiedSteps.trans (OCaml.Run.vsa_steps_iff.mpr ⟨ns, OCaml.Run.vsa_stepsN_iff.mp stackSteps⟩), post⟩
    · have empty : targets = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst targets
      exact ⟨first, Steps.refl first, firstPost.done_one⟩
  obtain ⟨done, doneSteps, donePost⟩ := doneRun
  obtain ⟨nr, after, returnSteps, post⟩ := closurerec_return donePost
  have firstRun : Steps ready first := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp firstSteps⟩
  have returnRun : Steps done after := OCaml.Run.vsa_steps_iff.mpr ⟨nr, OCaml.Run.vsa_stepsN_iff.mp returnSteps⟩
  exact ⟨after, setupSteps.append_steps (firstRun.trans (doneSteps.trans returnRun)), post⟩

end OCaml.Vm.Sim
