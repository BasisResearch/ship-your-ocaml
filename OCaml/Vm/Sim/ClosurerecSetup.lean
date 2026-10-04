import OCaml.Vm.Sim.ClosurerecPrefixMore
import OCaml.Vm.Sim.ClosurerecPrefixZero
import OCaml.Vm.Sim.ClosurerecReserve
import OCaml.Vm.Sim.ClosurerecInitializeMore
import OCaml.Vm.Sim.ClosurerecInitializeZero
import OCaml.Vm.Sim.ClosurerecReady

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Concrete G1 inputs for the allocation/capture half of recursive closure creation. -/
structure ClosurerecSetupInput (sp functions count a domain limit : Nat) (accu : BitVec 64) (c : Config) : Prop where
  young : closurerecSize functions count ≤ 256
  push : ClosurePushInput sp count accu
  nursery : ClosurerecNurseryInput sp functions count a domain limit accu c
  initializer : ClosurerecInitInput sp functions count a domain accu c

/-- The actual recursive allocation and capture paths reach their shared
metadata entry with exact writes, including zero captures and arbitrary copies. -/
theorem closurerec_setup {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat}
    {functions count : BitVec 32} {accu : BitVec 64}
    (h : ArmInput L P s .CLOSUREREC c pl cp sp high)
    (functionsOperand : OperandAt P pl (s.pc + 1) functions) (functionsPositive : 0 < functions.toInt)
    (countOperand : OperandAt P pl (s.pc + 2) count) (nonnegative : 0 ≤ count.toInt)
    (value : valWord pl s.accu = some accu)
    (space : ClosurerecSetupInput sp functions.toInt.toNat count.toInt.toNat a domain limit accu c) :
    ∃ after, Plus c after ∧ ClosurerecReady c pl s.pc sp functions.toInt.toNat count.toInt.toNat a domain accu after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have prefixRun : ∃ np prefixed, StepsN np d prefixed ∧
      ClosurerecPrefixed c pl s.pc sp functions.toInt.toNat count.toInt.toNat accu prefixed := by
    by_cases positive : 0 < count.toInt.toNat
    · exact closurerec_prefix_more h functionsOperand functionsPositive countOperand nonnegative space.young positive value space.push dp
    · exact closurerec_prefix_zero h functionsOperand functionsPositive countOperand nonnegative space.young (by omega) value space.push dp
  obtain ⟨np, prefixed, prefixSteps, prefixPost⟩ := prefixRun
  obtain ⟨nr, reserved, reserveSteps, reservation⟩ := closurerec_reserve space.nursery prefixPost
  have initRun : ∃ ni middle, StepsN ni reserved middle ∧
      ClosurerecInitialized c pl s.pc sp functions.toInt.toNat count.toInt.toNat a domain accu middle := by
    by_cases positive : 0 < count.toInt.toNat
    · exact closurerec_initialize_more space.nursery.nursery space.initializer positive reservation
    · exact closurerec_initialize_zero space.nursery.nursery space.initializer (by omega) reservation
  obtain ⟨ni, middle, initSteps, front⟩ := initRun
  have readyRun : ∃ copied, Steps middle copied ∧
      ClosurerecReady c pl s.pc sp functions.toInt.toNat count.toInt.toNat a domain accu copied := by
    by_cases positive : 0 < count.toInt.toNat
    · obtain ⟨copied, copySteps, back⟩ := closurerec_copy_run
        (space.initializer.copy_after space.push.room front) (front.copyRegisters positive).base
        middle (front.copy_start positive)
      exact ⟨copied, copySteps, front.ready_copy back⟩
    · exact ⟨middle, Steps.refl middle, front.ready_zero (by omega)⟩
  obtain ⟨copied, copySteps, ready⟩ := readyRun
  have setupRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr
    ⟨np + nr + ni, OCaml.Run.vsa_stepsN_iff.mp ((prefixSteps.append reserveSteps).append initSteps)⟩
  obtain ⟨n, whole⟩ := (setupRun.trans copySteps).toN
  exact ⟨n, copied, whole, ready⟩

end OCaml.Vm.Sim
