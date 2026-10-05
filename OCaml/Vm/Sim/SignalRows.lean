import OCaml.Vm.Sim.CheckSignals
import OCaml.Vm.Sim.DecodeFetch
import OCaml.Vm.Sim.StackRows

/-!
# The CHECK_SIGNALS row

Under the runtime-framing contract no signal is pending at a loop head
(`RuntimeFrame.quiet`), so CHECK_SIGNALS takes its fall-through path.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **CHECK_SIGNALS from the loop head.** -/
theorem check_signals_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0) (h : OCaml.LoopAt L P s c)
    (code : DispatchCode P s .CHECK_SIGNALS) (step : stepI P s ⟨.CHECK_SIGNALS, []⟩ = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨c', run, running⟩ := check_signals_step_arm stable input (rf.quiet c input.runtime) step
  exact ⟨c', run, h.of_plus run running⟩

/-- **The CHECK_SIGNALS row.** -/
theorem check_signals_row {L : OCaml.Layout} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0) :
    OCaml.OpArm P (OCaml.LoopAt L P) .CHECK_SIGNALS :=
  opArm_of_next0 (fun _ _ _ _ h code step => check_signals_next stable rf h code step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by cases step)

end OCaml.Vm.Sim
