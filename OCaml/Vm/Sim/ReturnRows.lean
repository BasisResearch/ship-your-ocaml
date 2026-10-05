import OCaml.Vm.Sim.Return
import OCaml.Vm.Sim.ApplyRows

/-!
# Loop-head simulation of RETURN

Both paths from `LoopAt`: with pending extra arguments RETURN re-enters the
accumulator's closure (its code field read through the placement); without,
it pops the three-word return frame (read windows from the stack geometry).
Two facts about the bytecode state stay named, because they are BcSem
reachability invariants rather than machine facts: the extra-argument count
fits a native long (`small`), and saved frame extra counts are nonnegative
(`savedNonnegative`; `APPLY` saves `Val.ofInt s.extra`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **RETURN n from the loop head.** -/
theorem return_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .RETURN)
    (fetch : P.code[s.pc + 1]? = some w)
    (small : s.extra < 2^63)
    (savedNonnegative : ∀ dest env (extra : BitVec 63) rest,
      s.stack.drop w.toInt.toNat = .code dest :: env :: .int extra :: rest → 0 ≤ extra.toInt)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.RETURN, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
  have unguarded := Res.unguard step
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  have operand := OperandAt.of_fetch input.geometry fetch
  have bound : w.toInt.toNat ≤ s.stack.length := by
    by_cases inside : w.toInt.toNat ≤ s.stack.length
    · exact inside
    · have bad : s.stack.length < w.toInt.toNat := by omega
      simp only [bad, ite_true] at unguarded
      cases unguarded
  have shape := unguarded
  simp only [show ¬ s.stack.length < w.toInt.toNat by omega, ite_false] at shape
  by_cases more : 0 < s.extra
  · simp only [more, ite_true] at shape
    obtain ⟨dest, sel⟩ := enter_next shape
    obtain ⟨l, a, k, field⟩ := field_selection input.toVmReprAt (by simp [roots]) sel
    obtain ⟨c', run, running⟩ := return_more_step_arm stable input operand nonnegative more small field
      (by simpa only [Nat.add_zero] using input.geometry.field_read field) step
    exact ⟨c', run, h.of_plus run running⟩
  · have noExtra : s.extra = 0 := by omega
    simp only [more, ite_false] at shape
    split at shape
    · rename_i dest env extra rest frame
      have len := congrArg List.length frame
      simp only [List.length_drop, List.length_cons] at len
      have rd : ∀ j, j < 3 → RamReadAt (sp + 8 * w.toInt.toNat + 8 * j) 8 := fun j hj => by
        simpa only [Nat.mul_add, Nat.add_assoc] using
          input.geometry.read input.stack (stack_space input.stack space)
            (i := w.toInt.toNat + j) (by omega)
      obtain ⟨c', run, running⟩ := return_frame_step_arm stable input operand nonnegative noExtra
        (savedNonnegative dest env extra rest frame) frame
        ⟨by simpa using rd 0 (by decide), by simpa using rd 1 (by decide), by simpa using rd 2 (by decide)⟩
        step
      exact ⟨c', run, h.of_plus run running⟩
    · cases shape

end OCaml.Vm.Sim
