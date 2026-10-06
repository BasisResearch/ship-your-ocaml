import OCaml.Vm.Sim.Apply1
import OCaml.Vm.Sim.Apply2
import OCaml.Vm.Sim.Apply3
import OCaml.Vm.Sim.OperandStackRows

/-!
# Loop-head simulations of APPLY1..APPLY3

The return frame and the moved arguments are written inside the VM stack
allocation (`StackGeometry.edit`); closure entry is ready because the new
frame stays above `stack_threshold` (`RuntimeFrame.enter`, from the budget's
threshold slack); the closure's code field is read through the placement.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem logInW_mem {ws : List W} {log : List WEntry} (inside : LogInW ws log) {e : WEntry}
    (member : e ∈ log) : InsideW ws e.1 e.2.1 := by
  induction log with
  | nil => cases member
  | cons x log ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact inside.1
    · exact ih inside.2 tail

theorem logInW_widen {ws : List W} {log : List WEntry} {lo hi : Nat} (inside : LogInW ws log)
    (sub : ∀ w ∈ ws, lo ≤ w.lo ∧ w.hi ≤ hi) : LogInW [⟨lo, hi⟩] log := by
  apply log_in_windows_of_mem
  intro e member
  have h := logInW_mem inside member
  clear inside member
  induction ws with
  | nil => exact False.elim h
  | cons w ws ih =>
    rcases h with here | tail
    · have := sub w (by simp)
      exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega⟩
    · exact ih (fun w' hw => sub w' (by simp [hw])) tail

/-- **APPLY's frame write is separated, writable and enters a ready closure**. -/
theorem ApplyWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high n : Nat} {env : BitVec 64} (g : ArmGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (positive : 1 ≤ n) (small : n ≤ 3)
    (bound : n ≤ s.stack.length)
    (space : 8 * (s.stack.length + 3) ≤ Layout.stackBytes) :
    ApplyWriteOk P s c pl cp sp high (stackWords c sp n) env := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hal := g.aligned
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have len : (stackWords c sp n).length = n := by simp [stackWords]
  have inside := apply_entries_in (args := stackWords c sp n) (sp - 24)
    (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) env (tag64 (BitVec.ofNat 63 s.extra))
    (by omega) (by omega)
  rw [len] at inside
  have wide : LogInW [stackWindow high] (applyFrameLog sp (stackWords c sp n)
      (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) env (tag64 (BitVec.ofNat 63 s.extra))) :=
    logInW_widen inside (by
      intro w hw
      simp only [List.mem_singleton] at hw
      subst hw
      simp only [stackWindow]
      omega)
  refine ⟨by omega, fun i hi => ?_, fun e member => ?_, g.edit wide, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩,
    .of_stack g.toStackGeometry wide, ⟨?_, ?_⟩⟩
  · rw [len] at hi
    exact g.read stack (by omega) (by omega)
  · have hin := logInW_mem inside member
    obtain ⟨⟨j, v⟩, -, rfl⟩ := List.mem_map.mp member
    simp only [InsideW, or_false] at hin
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, LibraryLayout.tohostAddr,
      Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega
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

theorem enter_next {s s' : St} {stack : List Val} {extra : Nat}
    (h : enter s stack extra = .next s') : ∃ dest, field? s.heap s.accu 0 = some (.code dest) := by
  unfold enter at h
  obtain ⟨v, hv, k⟩ := opt_next h
  cases v with
  | code dest => exact ⟨dest, hv⟩
  | _ => cases k

/-- Shared simulation of `APPLYn` from the loop head, given the generated
`applyn_step_arm`. -/
theorem apply_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0) (positive : 1 ≤ n) (small : n ≤ 3)
    (arm : ∀ pl cp sp high l a k dest env, WindowStable L.runtimeOk [⟨sp - 24, sp + 8 * n⟩] →
      ArmInput L P s op c pl cp sp high → n ≤ s.stack.length →
      FieldSelection s.heap pl s.accu 0 (.code dest) l a k → RamReadAt (a + 8 * k) 8 →
      EnterReady c (sp - 24) → valWord pl s.env = some env →
      ApplyWriteOk P s c pl cp sp high (stackWords c sp n) env →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op) (bound : n ≤ s.stack.length)
    (selected : ∃ dest, field? s.heap s.accu 0 = some (.code dest))
    (space : 8 * (s.stack.length + 3) + Layout.stackThresholdBytes ≤ Layout.stackBytes) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨dest, sel⟩ := selected
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, field⟩ := field_selection input.toVmReprAt (by simp [roots]) sel
  obtain ⟨env, -, envWord⟩ := input.env
  have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
  have hs := input.stack.1
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k dest env
    (rf.stackWindow _ _ (by rw [← same]; omega) (by rw [← same]; omega)) input bound field
    (by simpa only [Nat.add_zero] using input.geometry.field_read field)
    (rf.enter input (by have h1 := input.stack.1; have h2 := space; have h3 := input.geometry.statics; have h4 : 24 ≤ Layout.sym_bss_end := (by decide); show high - Layout.stackBytes + Layout.stackThresholdBytes ≤ sp - 24; omega)) envWord
    (ApplyWriteOk.of_geometry input.geometry.toArmGeometry input.stack positive small bound (by omega))
  exact ⟨c', run, h.of_plus run running⟩

/-- **APPLY1 from the loop head.** -/
theorem apply1_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .APPLY1)
    (space : 8 * (s.stack.length + 3) + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPLY1, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape : 1 ≤ s.stack.length ∧ ∃ dest, field? s.heap s.accu 0 = some (.code dest) := by
    cases hs : s.stack with
    | nil => simp [stepI, hs] at step
    | cons a1 r1 =>
      
      
      
        
        
        
          simp only [stepI, hs] at step
          exact ⟨by simp, enter_next step⟩
  exact apply_next (n := 1) rf (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ _ stable input bound field read ready envWord space =>
      apply1_step_arm stable input bound field read ready envWord space step)
    h code shape.1 shape.2 space

/-- **APPLY2 from the loop head.** -/
theorem apply2_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .APPLY2)
    (space : 8 * (s.stack.length + 3) + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPLY2, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape : 2 ≤ s.stack.length ∧ ∃ dest, field? s.heap s.accu 0 = some (.code dest) := by
    cases hs : s.stack with
    | nil => simp [stepI, hs] at step
    | cons a1 r1 =>
      cases r1 with
      | nil => simp [stepI, hs] at step
      | cons a2 r2 =>
        
        
        
          simp only [stepI, hs] at step
          exact ⟨by simp, enter_next step⟩
  exact apply_next (n := 2) rf (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ _ stable input bound field read ready envWord space =>
      apply2_step_arm stable input bound field read ready envWord space step)
    h code shape.1 shape.2 space

/-- **APPLY3 from the loop head.** -/
theorem apply3_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .APPLY3)
    (space : 8 * (s.stack.length + 3) + Layout.stackThresholdBytes ≤ Layout.stackBytes)
    (step : stepI P s ⟨.APPLY3, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape : 3 ≤ s.stack.length ∧ ∃ dest, field? s.heap s.accu 0 = some (.code dest) := by
    cases hs : s.stack with
    | nil => simp [stepI, hs] at step
    | cons a1 r1 =>
      cases r1 with
      | nil => simp [stepI, hs] at step
      | cons a2 r2 =>
        cases r2 with
        | nil => simp [stepI, hs] at step
        | cons a3 r3 =>
          simp only [stepI, hs] at step
          exact ⟨by simp, enter_next step⟩
  exact apply_next (n := 3) rf (by decide) (by decide)
    (fun _ _ _ _ _ _ _ _ _ stable input bound field read ready envWord space =>
      apply3_step_arm stable input bound field read ready envWord space step)
    h code shape.1 shape.2 space

end OCaml.Vm.Sim
