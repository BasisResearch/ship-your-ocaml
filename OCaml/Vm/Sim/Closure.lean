import OCaml.Vm.Sim.ClosurePrefixMore
import OCaml.Vm.Sim.ClosurePrefixZero
import OCaml.Vm.Sim.ClosureReserve
import OCaml.Vm.Sim.ClosureInitializeMore
import OCaml.Vm.Sim.ClosureInitializeZero
import OCaml.Vm.Sim.ClosureFinish

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The actual ordinary CLOSURE nursery constructor, including zero captures
and the generated arbitrary-count copy, with represented metadata and heap. -/
theorem closure_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest a domain limit : Nat}
    {count ofs : BitVec 32} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk c (closureAllocationLog c pl sp count.toInt.toNat dest a domain accu))
    (h : ArmInput L P s .CLOSURE c pl cp sp high)
    (countOperand : OperandAt P pl (s.pc + 1) count) (offsetOperand : OperandAt P pl (s.pc + 2) ofs)
    (nonnegative : 0 ≤ count.toInt) (jump : target s.pc 1 ofs.toInt = some dest)
    (value : valWord pl s.accu = some accu)
    (space : ClosureAllocInput P s c pl cp sp high count.toInt.toNat dest a domain limit accu) :
    ∃ after, Plus c after ∧ Running L P (closureState s count.toInt.toNat dest) after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have prefixRun : ∃ np prefixed, StepsN np d prefixed ∧ ClosurePrefixed c pl s.pc sp count.toInt.toNat accu prefixed := by
    by_cases positive : 0 < count.toInt.toNat
    · exact closure_prefix_more h countOperand nonnegative space.young positive value space.push dp
    · exact closure_prefix_zero h countOperand nonnegative space.young (by omega) value space.push dp
  obtain ⟨np, prefixed, prefixSteps, prefixPost⟩ := prefixRun
  obtain ⟨nr, reserved, reserveSteps, reservation⟩ := closure_reserve space.nursery prefixPost
  have initRun : ∃ ni middle, StepsN ni reserved middle ∧ ClosureInitialized c pl s.pc sp count.toInt.toNat a domain accu middle := by
    by_cases positive : 0 < count.toInt.toNat
    · exact closure_initialize_more space.nursery.nursery space.initializer positive reservation
    · exact closure_initialize_zero space.nursery.nursery space.initializer (by omega) reservation
  obtain ⟨ni, middle, initSteps, front⟩ := initRun
  have readyRun : ∃ copied, Steps middle copied ∧ ClosureReady c pl s.pc sp count.toInt.toNat a domain accu copied := by
    by_cases positive : 0 < count.toInt.toNat
    · obtain ⟨copied, copySteps, back⟩ := closure_copy_run (space.initializer.copy_after space.push.room front) middle (front.copy_start positive)
      exact ⟨copied, copySteps, front.ready_copy back⟩
    · exact ⟨middle, Steps.refl middle, front.ready_zero (by omega)⟩
  obtain ⟨copied, copySteps, ready⟩ := readyRun
  obtain ⟨nf, after, finishSteps, running⟩ := closure_finish runtime h value offsetOperand jump
    space.toClosureWriteOk space.push.room space.metadata ready
  have setupRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr
    ⟨np + nr + ni, OCaml.Run.vsa_stepsN_iff.mp ((prefixSteps.append reserveSteps).append initSteps)⟩
  have finishRun : Steps copied after := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp finishSteps⟩
  obtain ⟨n, whole⟩ := (setupRun.trans (copySteps.trans finishRun)).toN
  exact ⟨n, after, whole, running⟩

/-- A successful bytecode CLOSURE step is implemented by the represented nursery path. -/
theorem closure_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest a domain limit : Nat}
    {count ofs : BitVec 32} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk c (closureAllocationLog c pl sp count.toInt.toNat dest a domain accu))
    (h : ArmInput L P s .CLOSURE c pl cp sp high)
    (countOperand : OperandAt P pl (s.pc + 1) count) (offsetOperand : OperandAt P pl (s.pc + 2) ofs)
    (nonnegative : 0 ≤ count.toInt) (jump : target s.pc 1 ofs.toInt = some dest)
    (value : valWord pl s.accu = some accu)
    (space : ClosureAllocInput P s c pl cp sp high count.toInt.toNat dest a domain limit accu)
    (step : stepI P s ⟨.CLOSURE, [count.toInt, ofs.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  rw [← closure_state_of_step space.bound jump step]
  exact closure_arm runtime h countOperand offsetOperand nonnegative jump value space

end OCaml.Vm.Sim
