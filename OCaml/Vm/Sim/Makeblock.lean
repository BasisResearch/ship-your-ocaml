import OCaml.Vm.Sim.MakeblockReserve
import OCaml.Vm.Sim.MakeblockInitializeMore
import OCaml.Vm.Sim.MakeblockInitializeOne
import OCaml.Vm.Sim.MakeblockFinishMore
import OCaml.Vm.Sim.MakeblockFinishOne

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Generic MAKEBLOCK's actual G1 nursery path, including the single-field
branch and the arbitrary-count forward copy. -/
theorem makeblock_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat} {size tag : BitVec 32} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk c (makeblockLog c sp size.toInt.toNat tag.toInt.toNat a domain accu))
    (h : ArmInput L P s .MAKEBLOCK c pl cp sp high)
    (sizeOperand : OperandAt P pl (s.pc + 1) size) (tagOperand : OperandAt P pl (s.pc + 2) tag)
    (sizeNonnegative : 0 ≤ size.toInt) (tagNonnegative : 0 ≤ tag.toInt)
    (nursery : size.toInt.toNat ≤ 256) (value : valWord pl s.accu = some accu)
    (space : MakeblockInput P s c pl cp sp high size.toInt.toNat tag.toInt.toNat a domain limit accu)
    (initializer : MakeblockInitInput sp size.toInt.toNat tag.toInt.toNat a domain accu c) :
    ∃ after, Plus c after ∧ Running L P (makeblockState s 3 size.toInt.toNat tag.toInt.toNat) after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nr, reserved, reserveSteps, reservation⟩ := makeblock_reserve h sizeOperand tagOperand sizeNonnegative nursery space dp
  by_cases more : 1 < size.toInt.toNat
  · obtain ⟨ni, middle, initSteps, front⟩ := makeblock_initialize_more h value tagNonnegative more space reservation
    obtain ⟨copied, copySteps, back⟩ := makeblock_copy_run (initializer.copy_after front) middle (front.copy_start more)
    obtain ⟨nf, after, finishSteps, running⟩ := makeblock_finish_more runtime h value space.toMakeblockWriteOk more front back
    have setupRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr
      ⟨nr + ni, OCaml.Run.vsa_stepsN_iff.mp (reserveSteps.append initSteps)⟩
    have finishRun : Steps copied after := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp finishSteps⟩
    obtain ⟨n, whole⟩ := (setupRun.trans (copySteps.trans finishRun)).toN
    exact ⟨n, after, whole, running⟩
  · have one : size.toInt.toNat = 1 := by have positive := space.positive; omega
    obtain ⟨ni, middle, initSteps, front⟩ := makeblock_initialize_one h value tagNonnegative one space reservation
    obtain ⟨nf, after, finishSteps, running⟩ := makeblock_finish_one runtime h value space.toMakeblockWriteOk one front
    exact ⟨nr + ni + nf, after, (reserveSteps.append initSteps).append finishSteps, running⟩

/-- The successful generic bytecode constructor agrees with the represented block. -/
theorem makeblock_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit : Nat} {size tag : BitVec 32} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk c (makeblockLog c sp size.toInt.toNat tag.toInt.toNat a domain accu))
    (h : ArmInput L P s .MAKEBLOCK c pl cp sp high)
    (sizeOperand : OperandAt P pl (s.pc + 1) size) (tagOperand : OperandAt P pl (s.pc + 2) tag)
    (sizeNonnegative : 0 ≤ size.toInt) (tagNonnegative : 0 ≤ tag.toInt)
    (nursery : size.toInt.toNat ≤ 256) (value : valWord pl s.accu = some accu)
    (space : MakeblockInput P s c pl cp sp high size.toInt.toNat tag.toInt.toNat a domain limit accu)
    (initializer : MakeblockInitInput sp size.toInt.toNat tag.toInt.toNat a domain accu c)
    (step : stepI P s ⟨.MAKEBLOCK, [size.toInt, tag.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have enough : ¬ s.stack.length < size.toInt.toNat - 1 := by have bound := space.bound; omega
  have nonzero : ¬ size.toInt.toNat = 0 := by have positive := space.positive; omega
  have state : makeblockState s 3 size.toInt.toNat tag.toInt.toNat = s' := by
    simpa only [stepI, makeBlock, nonzero, enough, ite_false,
      makeblockState, makeblockObject, Res.next.injEq] using step
  rw [← state]
  exact makeblock_arm runtime h sizeOperand tagOperand sizeNonnegative tagNonnegative nursery value space initializer

end OCaml.Vm.Sim
