import OCaml.Vm.Sim.ApptermSetup
import OCaml.Vm.Sim.ApptermFinish

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Generic APPTERM composes the generated prefix, proved arbitrary-count
backward-copy loop and generated closure-entry suffix. -/
theorem appterm_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {count slots : BitVec 32}
    (stable : WindowStable L.runtimeOk
      [⟨tailcallStart sp count.toInt.toNat slots.toInt.toNat, sp + 8 * slots.toInt.toNat⟩])
    (h : ArmInput L P s .APPTERM c pl cp sp high)
    (countAt : OperandAt P pl (s.pc + 1) count) (slotsAt : OperandAt P pl (s.pc + 2) slots)
    (positive : 0 < count.toInt)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8)
    (ready : EnterReady c (tailcallStart sp count.toInt.toNat slots.toInt.toNat))
    (space : ApptermWriteOk P s c pl cp sp high count.toInt.toNat slots.toInt.toNat) :
    ∃ after, Plus c after ∧ Running L P (tailcallState s count.toInt.toNat slots.toInt.toNat dest) after := by
  have slotsNonnegative : 0 ≤ slots.toInt := by have fits := space.fits; omega
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nf, middle, prefixSteps, front⟩ := appterm_setup h countAt slotsAt positive slotsNonnegative space dp
  obtain ⟨copied, copySteps, back⟩ := backward_copy_run (space.copy_after front) middle front.copy
  obtain ⟨nb, after, suffixSteps, running⟩ := appterm_finish stable h (by omega) field geometry ready space front back
  have frontRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp prefixSteps⟩
  have backRun : Steps copied after := OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp suffixSteps⟩
  obtain ⟨n, whole⟩ := (frontRun.trans (copySteps.trans backRun)).toN
  exact ⟨n, after, whole, running⟩

/-- Successful APPTERM supplies the positive count and selects the represented
tail-call state; machine geometry and runtime framing remain explicit. -/
theorem appterm_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {count slots : BitVec 32}
    (stable : WindowStable L.runtimeOk
      [⟨tailcallStart sp count.toInt.toNat slots.toInt.toNat, sp + 8 * slots.toInt.toNat⟩])
    (h : ArmInput L P s .APPTERM c pl cp sp high)
    (countAt : OperandAt P pl (s.pc + 1) count) (slotsAt : OperandAt P pl (s.pc + 2) slots)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8)
    (ready : EnterReady c (tailcallStart sp count.toInt.toNat slots.toInt.toNat))
    (space : ApptermWriteOk P s c pl cp sp high count.toInt.toNat slots.toInt.toNat)
    (step : stepI P s ⟨.APPTERM, [count.toInt, slots.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have positive : 0 < count.toInt := by
    by_cases positive : 0 < count.toInt
    · exact positive
    · have zero : count.toInt.toNat = 0 := by omega
      simp only [stepI, zero, true_or, ite_true] at step
      cases step
  have valid : ¬ (count.toInt.toNat = 0 ∨ slots.toInt.toNat < count.toInt.toNat ∨
      s.stack.length < slots.toInt.toNat) := by have fits := space.fits; have bound := space.bound; omega
  have state : tailcallState s count.toInt.toNat slots.toInt.toNat dest = s' := by
    simpa only [stepI, valid, ite_false, enter, field.selected, opt, tailcallState, Res.next.injEq] using step
  rw [← state]
  exact appterm_arm stable h countAt slotsAt positive field geometry ready space

end OCaml.Vm.Sim
