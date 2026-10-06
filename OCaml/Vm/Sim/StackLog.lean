import OCaml.Vm.Sim.ApplyRows
import OCaml.Vm.Sim.Appterm1
import OCaml.Vm.Sim.Appterm2
import OCaml.Vm.Sim.Appterm3

/-!
# Certificates for word writes inside the VM stack allocation

`StackLogOk` bundles every separation and geometry fact an arm needs for a
write log confined to the stack allocation: each store is writable RAM, the
non-stack payload, the closure-entry reads, the image and the primitive
bindings are untouched. `StackLogOk.of_window` derives all of it from the
stack geometry once, for any log whose stores are aligned words inside a
window of the allocation.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Everything a stack-confined write log must satisfy. -/
structure StackLogOk (log : List WEntry) (P : Prog) (s : St) (c : Config) (pl : Place)
    (cp : ChanPlace) (high : Nat) : Prop where
  writes : ∀ entry ∈ log, RamWriteAt entry.1 entry.2.1
  payload : StackEditOutside log P s c pl cp high
  enter : EnterOutside log c
  image : ImageOutside log
  young : YoungOutside log c
  bindings : BindingsOutside log P c

/-- **One derivation for every stack-confined log.** -/
theorem StackLogOk.of_window {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high lo hi : Nat} {log : List WEntry} (g : ArmGeometry P s c pl cp high)
    (inside : LogInW [⟨lo, hi⟩] log) (low : high - Layout.stackBytes ≤ lo) (top : hi ≤ high)
    (words : ∀ entry ∈ log, entry.2.1 = 8 ∧ entry.1 % 8 = 0) :
    StackLogOk log P s c pl cp high := by
  have ht := g.top
  have hg := g.statics
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have wide : LogInW [stackWindow high] log :=
    logInW_widen inside (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [stackWindow]
      omega)
  refine ⟨fun e member => ?_, g.edit wide, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, .of_stack g.toStackGeometry wide,
    ⟨?_, ?_⟩⟩
  · have hin := logInW_mem inside member
    obtain ⟨width, aligned⟩ := words e member
    simp only [InsideW, or_false] at hin
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, LibraryLayout.tohostAddr,
      Layout.sym_tohost, Layout.sym_bss_end, width] at * <;> omega
  · exact outLRange_of_windows wide (stackWindow_static g.statics (by decide))
  · apply outLRange_of_windows wide
    have hd := g.domain.1
    have off : Layout.off_stack_threshold + 8 ≤ Layout.domainStateBytes := by decide
    exact ⟨by simp only [stackWindow] at hd ⊢; omega, trivial⟩
  · exact outLRange_of_windows wide (stackWindow_static g.statics (by decide))
  · exact outLRange_of_windows wide (stackWindow_static g.statics (by decide))
  · exact outLRange_of_windows wide (stackWindow_static g.statics (by decide))
  · exact outLRange_of_windows wide (stackWindow_static g.statics (by decide))
  · exact fun j name hj => outLRange_of_windows wide (g.primitives j name hj)

/-- Indexed word logs from an aligned base are aligned word stores. -/
theorem indexedLog_words {base : Nat} {entries : List (Nat × BitVec 64)} (aligned : base % 8 = 0) :
    ∀ entry ∈ indexedLog base entries, entry.2.1 = 8 ∧ entry.1 % 8 = 0 := by
  intro e member
  obtain ⟨⟨j, v⟩, -, rfl⟩ := List.mem_map.mp member
  exact ⟨rfl, by simp only; omega⟩

/-- **The tail-call argument move is separated and writable.** -/
theorem TailcallWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high n slots : Nat} (g : ArmGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (fits : n ≤ slots) (bound : slots ≤ s.stack.length)
    (space : 8 * s.stack.length ≤ Layout.stackBytes) :
    TailcallWriteOk P s c pl cp sp high slots (stackWords c sp n) := by
  have hs := stack.1
  have ha := g.aligned
  have len : (stackWords c sp n).length = n := by simp [stackWords]
  have inside := value_log_in (tailcallStart sp (stackWords c sp n).length slots) (stackWords c sp n)
  have ok := StackLogOk.of_window g inside (by unfold tailcallStart; omega)
    (by unfold tailcallStart; omega) (indexedLog_words (by unfold tailcallStart; omega))
  exact ⟨by omega, bound, fun i hi => g.read stack (by omega) (by omega),
    ok.writes, ok.payload, ok.enter, ok.image, ok.young, ok.bindings⟩

/-- Shared simulation of `APPTERMn` from the loop head. -/
theorem appterm_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n slots high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (arm : ∀ pl cp sp high l a k dest,
      WindowStable L.runtimeOk [⟨tailcallStart sp n slots, sp + 8 * slots⟩] →
      ArmInput L P s op c pl cp sp high →
      FieldSelection s.heap pl s.accu 0 (.code dest) l a k → RamReadAt (a + 8 * k) 8 →
      EnterReady c (tailcallStart sp n slots) →
      TailcallWriteOk P s c pl cp sp high slots (stackWords c sp n) →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op) (fits : n ≤ slots)
    (bound : slots ≤ s.stack.length)
    (selected : ∃ dest, field? s.heap s.accu 0 = some (.code dest))
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨dest, sel⟩ := selected
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, field⟩ := field_selection input.toVmReprAt (by simp [roots]) sel
  have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
  have hs := input.stack.1
  have hg := input.geometry.statics
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k dest
    (rf.stackWindow _ _ (by rw [← same]; unfold tailcallStart; omega) (by rw [← same]; omega)) input
    field (by simpa only [Nat.add_zero] using input.geometry.field_read field)
    (rf.enter input (by unfold tailcallStart; omega))
    (TailcallWriteOk.of_geometry input.geometry.toArmGeometry input.stack fits bound (by omega))
  exact ⟨c', run, h.of_plus run running⟩

/-- **APPTERM1 from the loop head.** -/
theorem appterm1_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .APPTERM1)
    (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPTERM1, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · cases shape
  · rename_i valid
    have nonnegative : 0 ≤ w.toInt := by omega
    exact appterm_next (n := 1) rf
      (fun _ _ _ _ _ _ _ _ stable input field read ready space =>
        appterm1_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) nonnegative
          field read ready space step)
      h code (by omega) (by omega) (enter_next shape) space

/-- **APPTERM2 from the loop head.** -/
theorem appterm2_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .APPTERM2)
    (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPTERM2, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · cases shape
  · rename_i valid
    have nonnegative : 0 ≤ w.toInt := by omega
    exact appterm_next (n := 2) rf
      (fun _ _ _ _ _ _ _ _ stable input field read ready space =>
        appterm2_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) nonnegative
          field read ready space step)
      h code (by omega) (by omega) (enter_next shape) space

/-- **APPTERM3 from the loop head.** -/
theorem appterm3_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {w : BitVec 32}
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .APPTERM3)
    (fetch : P.code[s.pc + 1]? = some w)
    (space : 8 * s.stack.length + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPTERM3, [w.toInt]⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · cases shape
  · rename_i valid
    have nonnegative : 0 ≤ w.toInt := by omega
    exact appterm_next (n := 3) rf
      (fun _ _ _ _ _ _ _ _ stable input field read ready space =>
        appterm3_step_arm stable input (OperandAt.of_fetch input.geometry.toArmGeometry fetch) nonnegative
          field read ready space step)
      h code (by omega) (by omega) (enter_next shape) space

end OCaml.Vm.Sim
