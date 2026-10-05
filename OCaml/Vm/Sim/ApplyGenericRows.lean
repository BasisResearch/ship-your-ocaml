import OCaml.Vm.Sim.Apply
import OCaml.Vm.Sim.Appterm
import OCaml.Vm.Sim.StackLog

/-!
# Loop-head simulations of the generic APPLY n and APPTERM n s

APPLY n only enters the closure (the caller pushed the frame with
PUSH_RETADDR). APPTERM n s moves the `n` arguments over the `s`-word frame by
a backward copy confined to the VM stack allocation (`StackLogOk.of_window`
on the reversed copy log).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **APPLY n from the loop head.** -/
theorem apply_generic_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .APPLY)
    (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPLY, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · cases shape
  · obtain ⟨dest, sel⟩ := enter_next shape
    obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
    obtain ⟨l, a, k, field⟩ := field_selection input.toVmReprAt (by simp [roots]) sel
    have hs := input.stack.1
    have hg := input.geometry.statics
    obtain ⟨c', run, running⟩ := apply_step_arm stable input (OperandAt.of_fetch input.geometry fetch)
      field (by simpa only [Nat.add_zero] using input.geometry.field_read field)
      (rf.enter input (by omega)) step
    exact ⟨c', run, h.of_plus run running⟩

theorem logInW_reverse {ws : List W} {log : List WEntry} (inside : LogInW ws log) :
    LogInW ws log.reverse :=
  log_in_windows_of_mem fun e member => logInW_mem inside (List.mem_reverse.mp member)

/-- **APPTERM's backward copy is separated, readable and writable.** -/
theorem ApptermWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high count slots : Nat} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (positive : 0 < count) (fits : count ≤ slots)
    (bound : slots ≤ s.stack.length) (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    ApptermWriteOk P s c pl cp sp high count slots := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have len : (stackWords c sp count).length = count := by simp [stackWords]
  have forward := value_log_in (tailcallStart sp count slots) (stackWords c sp count)
  rw [len] at forward
  have join : tailcallStart sp count slots + 8 * count = sp + 8 * slots := by
    unfold tailcallStart; omega
  rw [join] at forward
  have inside : LogInW [⟨tailcallStart sp count slots, sp + 8 * slots⟩]
      (reverseCopyLog (tailcallStart sp count slots) (stackWords c sp count) 0) := by
    simpa only [reverseCopyLog, List.drop_zero] using logInW_reverse forward
  have ok := StackLogOk.of_window g inside (by unfold tailcallStart; omega) (by omega) (by
    intro e member
    simp only [reverseCopyLog, List.drop_zero, List.mem_reverse] at member
    exact indexedLog_words (by unfold tailcallStart; omega) e member)
  refine ⟨⟨fits, bound, ok.payload, ok.image, ok.bindings, inside⟩, ⟨by omega, by unfold tailcallStart; omega,
    by rw [len]; omega, by rw [len]; omega, by rw [len]; unfold tailcallStart; omega,
    fun i hi => g.read stack (by omega) (by rw [len] at hi; omega), fun i hi => ?_, ok.image,
    fun i x hx => ?_⟩, ok.enter⟩
  · rw [len] at hi
    unfold tailcallStart
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, LibraryLayout.tohostAddr,
      Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega
  · simp only [stackWords] at hx
    simp at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.getElem?_eq_some_iff] at hj
    obtain ⟨_, hj⟩ := hj
    simp at hj
    rw [hj]

/-- **APPTERM n s from the loop head.** -/
theorem appterm_generic_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {count slots : BitVec 32} {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .APPTERM)
    (fetchCount : P.code[s.pc + 1]? = some count) (fetchSlots : P.code[s.pc + 2]? = some slots)
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPTERM, [count.toInt, slots.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · cases shape
  · rename_i valid
    obtain ⟨dest, sel⟩ := enter_next shape
    obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
    obtain ⟨l, a, k, field⟩ := field_selection input.toVmReprAt (by simp [roots]) sel
    have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
    have hs := input.stack.1
    have hg := input.geometry.statics
    obtain ⟨c', run, running⟩ := appterm_step_arm
      (rf.stackWindow _ _ (by rw [← same]; unfold tailcallStart; omega) (by rw [← same]; omega)) input
      (OperandAt.of_fetch input.geometry fetchCount) (OperandAt.of_fetch input.geometry fetchSlots)
      field (by simpa only [Nat.add_zero] using input.geometry.field_read field)
      (rf.enter input (by unfold tailcallStart; omega))
      (ApptermWriteOk.of_geometry input.geometry input.stack (by omega) (by omega) (by omega) (by omega))
      step
    exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
