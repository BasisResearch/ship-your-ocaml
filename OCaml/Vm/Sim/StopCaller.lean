import OCaml.Vm.Sim.StopExit
import OCaml.Vm.Sim.CamlMainReturn
import OCaml.Vm.Sim.MainExit
import OCaml.Vm.Sim.EntryFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Startup's enclosing caml_main frame survives the interpreter's final stores. -/
structure StopCallerReady (nativeSp : Nat) (interpSaved mainSaved : Nat → BitVec 64)
    (value vmSp : BitVec 64) (c : Config) : Prop where
  interpreterReturn : interpSaved 1 = 0x80004ff8#64
  mainReturn : mainSaved 1 = 0x80001df0#64
  ordinary : value &&& 3#64 ≠ 2#64
  frame : CamlMainSavedFrame (nativeSp + Layout.interpFrameBytes) mainSaved c
  outside : ∀ r ∈ Layout.camlMainSavedRegs, OutLRange (stopLog nativeSp vmSp c)
    (nativeSp + Layout.interpFrameBytes + Layout.camlMainSaveOffset r) 8

/-- STOP and both caller boundaries have reached caml_do_exit(0). -/
structure StopExitCallPost (before : Config) (nativeSp : Nat) (vmSp : BitVec 64) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (0x8001c5c8#64)
  stack : gpr after 2 = some (BitVec.ofNat 64 (nativeSp + Layout.interpFrameBytes + Layout.camlMainFrameBytes))
  status : gpr after 10 = some 0#64
  memory : after.σ.mem = writeLog before.σ.mem (stopLog nativeSp vmSp before)
  output : after.σ.sailOutput = before.σ.sailOutput
  /-- main's call of caml_main returns here (caml_do_exit never returns) -/
  returnAddress : gpr after 1 = some 0x80001df8#64
  /-- the callee-saved registers caml_do_exit's run reads are present: s0–s4
  restored by caml_main's epilogue, s5–s10 by the interpreter's -/
  present : ∀ n ∈ [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26], (gprGet after.σ n).isSome

/-- Run both actual native callers after STOP returns to caml_main. -/
theorem stop_callers {nativeSp : Nat} {interpSaved mainSaved : Nat → BitVec 64}
    {value vmSp : BitVec 64} {before middle : Config}
    (ready : StopCallerReady nativeSp interpSaved mainSaved value vmSp before)
    (returned : StopReturnPost before nativeSp interpSaved value vmSp middle) :
    ∃ count after, StepsN count middle after ∧ StopExitCallPost before nativeSp vmSp after := by
  have mainInput : CamlMainReturnInput (nativeSp + Layout.interpFrameBytes) mainSaved value middle := {
    good := returned.good, image := returned.image, tick := returned.tick
    pc := by simpa only [ready.interpreterReturn] using returned.pc
    frame := ready.frame.frame ready.outside returned.memory
    stack := returned.stack
    ordinary := ready.ordinary
    value := returned.value
    aligned := by rw [ready.mainReturn]; decide }
  obtain ⟨mainCount, mainAfter, mainRun, mainPost⟩ := caml_main_return mainInput
  have mainPc : pcOf mainAfter = some (0x80001df0#64) := by
    simpa only [ready.mainReturn] using mainPost.pc
  obtain ⟨exitCount, after, exitRun, exitPost⟩ := main_exit ⟨mainPost.good, mainPost.image, mainPost.tick, mainPc⟩
  refine ⟨mainCount + exitCount, after, mainRun.append exitRun, exitPost.good, exitPost.image,
    exitPost.tick, exitPost.pc, (exitPost.frame.frame _ (by decide)).trans mainPost.stack,
    exitPost.status, exitPost.memory.trans (mainPost.memory.trans returned.memory),
    exitPost.frame.out.trans (mainPost.frame.out.trans returned.output), exitPost.returnAddress, ?_⟩
  have keepExit := exitPost.frame.gpr_list (L := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26])
    (by decide +kernel)
  have keepMain := mainPost.frame.gpr_list (L := [21, 22, 23, 24, 25, 26]) (by decide +kernel)
  have main (n : Nat) (hn : n ∈ Layout.camlMainSavedRegs) : (gprGet mainAfter.σ n).isSome := by
    have m := mainPost.registers n hn
    change gprGet _ _ = _ at m
    rw [m]; rfl
  have interp (n : Nat) (hn : n ∈ [21, 22, 23, 24, 25, 26]) : (gprGet mainAfter.σ n).isSome := by
    have m := returned.registers n (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
      simp only [Layout.interpSavedRegs, List.mem_cons, List.mem_nil_iff, or_false]
      omega)
    change gprGet _ _ = _ at m
    rw [keepMain n hn, m]; rfl
  intro n hn
  rw [keepExit n hn]
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact main _ (by decide)
    | exact interp _ (by decide)

/-- The remaining primitive/runtime exit summary, now at its actual call site.
The caml_do_exit implementation (debugger, signal termination and libc/HTIF
exit) must supply this named machine obligation. -/
structure StopDoExitSummary (before : Config) (nativeSp : Nat) (vmSp : BitVec 64) (output : String) : Prop where
  run : ∀ after, StopExitCallPost before nativeSp vmSp after → Halts after output 0

/-- The caller continuation follows from the proved native returns and the exit callee summary. -/
theorem stop_exit_continuation_of_do_exit {nativeSp : Nat} {interpSaved mainSaved : Nat → BitVec 64}
    {value vmSp : BitVec 64} {before : Config} {output : String}
    (ready : StopCallerReady nativeSp interpSaved mainSaved value vmSp before)
    (exit : StopDoExitSummary before nativeSp vmSp output) :
    StopExitContinuation before nativeSp interpSaved value vmSp output := by
  constructor
  intro middle returned
  obtain ⟨count, after, run, post⟩ := stop_callers ready returned
  exact Halts.of_steps run.toSteps (exit.run after post)

end OCaml.Vm.Sim
