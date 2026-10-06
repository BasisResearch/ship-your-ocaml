import OCaml.Vm.Sim.ReturnMore
import OCaml.Vm.Sim.ReturnFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Match RETURN's extra-argument semantic branch to its generated closure-entry path. -/
theorem return_more_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {count : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .RETURN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (positive : 0 < s.extra) (small : s.extra < 2^63)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8)
    (step : stepI P s ⟨.RETURN, [count.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have bound : count.toInt.toNat ≤ s.stack.length := by
    by_cases bound : count.toInt.toNat ≤ s.stack.length
    · exact bound
    · have bad : s.stack.length < count.toInt.toNat := by omega
      have step := Res.unguard (Res.unguard step); simp only [stepI, bad, ite_true] at step
      cases step
  have state : {s with pc := dest, env := s.accu, extra := s.extra - 1, stack := s.stack.drop count.toInt.toNat} = s' := by
    simpa only [stepI, show ¬ s.stack.length < count.toInt.toNat by omega, ite_false,
      positive, ite_true, enter, field.selected, opt, Res.next.injEq] using Res.unguard (Res.unguard step)
  rw [← state]
  exact return_more_arm stable h operand nonnegative bound positive small field geometry

/-- Match RETURN's saved-caller semantic branch to its generated frame reads. -/
theorem return_frame_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {count : BitVec 32}
    {env : Val} {extra : BitVec 63} {rest : List Val}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .RETURN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (noExtra : s.extra = 0) (savedNonnegative : 0 ≤ extra.toInt)
    (stack : s.stack.drop count.toInt.toNat = .code dest :: env :: .int extra :: rest)
    (reads : ReturnFrameReads (sp + 8 * count.toInt.toNat))
    (step : stepI P s ⟨.RETURN, [count.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have bound : count.toInt.toNat ≤ s.stack.length := by
    have len := congrArg List.length stack
    simp only [List.length_drop, List.length_cons] at len
    omega
  have remainder : s.stack.drop (count.toInt.toNat + 3) = rest := by
    have dropped := congrArg (List.drop 3) stack
    simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using dropped
  have state : {s with pc := dest, env := env, extra := extra.toNat, stack := s.stack.drop (count.toInt.toNat + 3)} = s' := by
    simpa only [stepI, show ¬ s.stack.length < count.toInt.toNat by omega, ite_false,
      noExtra, Nat.lt_irrefl, stack, remainder, show ¬ extra.toInt < 0 by omega, ite_false,
      Res.next.injEq] using Res.unguard (Res.unguard step)
  rw [← state]
  exact return_frame_arm stable h operand nonnegative noExtra savedNonnegative stack reads

end OCaml.Vm.Sim
