import OCaml.Vm.Sim.Restart
import OCaml.Vm.Sim.StackLog

/-!
# Loop-head simulation of RESTART

The partial closure's saved arguments are copied below `sp` into the free
part of the VM stack allocation (`StackLogOk.of_window`); the closure block's
header, environment and argument fields are read through its placement. The
successor's stack bound comes from the budget (`Fits` of the successor).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **RESTART's reads and copy are in RAM and separated.** -/
theorem RestartInput.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a tag : Nat} {fields : List Val} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack) (block : BlockSelection s.heap pl s.env l a tag fields)
    (lower : 3 ≤ fields.length)
    (space : 8 * (s.stack.length + (fields.length - 3)) ≤ Layout.stackBytes) :
    RestartInput P s c pl cp sp high a fields := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have ha := g.aligned
  have lo := g.heapLow l a _ block.placed block.object
  have hi := g.heapArena l a _ block.placed block.object
  simp only [Obj.wosize] at hi
  have hb : Layout.sym_tohost + 16 ≤ Layout.sym_bss_end := by decide
  have len : (stackWords c (a + 24) (fields.length - 3)).length = fields.length - 3 := by
    simp [stackWords]
  have inside := value_log_in (restartStart sp fields) (stackWords c (a + 24) (fields.length - 3))
  rw [len] at inside
  have ok := StackLogOk.of_window g inside (by unfold restartStart; omega)
    (by unfold restartStart; omega) (indexedLog_words (by unfold restartStart; omega))
  refine ⟨⟨by omega, ok.payload, ok.image, ok.bindings⟩, by omega, ?_, ?_, lower, by
      simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at *; omega, fun i hi' => ?_,
    fun i hi' => ?_⟩
  all_goals first
    | (refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_bss_end, Layout.sym_tohost,
        Vsa.Sim.DlHeap.heapEnd] at * <;> omega)
    | (unfold restartStart
       refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [tohostAddr, LibraryLayout.tohostAddr,
        Layout.sym_tohost, Layout.sym_bss_end] at * <;> omega)

/-- **RESTART from the loop head.** -/
theorem restart_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 : Nat}
    (rf : RuntimeFrame L high0) (h : OCaml.LoopAt L P s c) (code : DispatchCode P s .RESTART)
    (space : 8 * s'.stack.length ≤ Layout.stackBytes)
    (step : stepI P s ⟨.RESTART, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  have shape := step
  simp only [stepI] at shape
  split at shape
  · rename_i l henv
    split at shape
    · rename_i tag fields object
      split at shape
      · cases shape
      · rename_i valid
        cases shape
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨x, -, envWord⟩ := input.env
        rw [henv] at envWord
        simp only [valWord] at envWord
        cases placed : pl.φ l with
        | none => rw [placed] at envWord; cases envWord
        | some a =>
          have block : BlockSelection s.heap pl s.env l a tag fields := ⟨henv, placed, object⟩
          have environment : fields[2]? = some (fields.getD 2 .unit) := by
            simp only [List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_getElem (by omega)]
            rfl
          have same : high = high0 := input.stackHigh.symm.trans (rf.stackHigh c input.runtime)
          have hs := input.stack.1
          have hg := input.geometry.statics
          simp only [List.length_append, List.length_drop] at space
          obtain ⟨c', run, running⟩ := restart_step_arm
            (rf.stackWindow _ _ (by rw [← same]; unfold restartStart; omega) (by rw [← same]; omega))
            input block environment
            (RestartInput.of_geometry input.geometry input.stack block (by omega) (by omega)) step
          exact ⟨c', run, h.of_plus run running⟩
    · cases shape
  · cases shape

end OCaml.Vm.Sim
