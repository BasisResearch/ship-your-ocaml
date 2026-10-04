import OCaml.Vm.Sim.StopExit
import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.ReadOnly

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim

/-- The complete STOP arm starts at the represented loop head and returns to
its native caller. Saved invocation geometry is supplied separately by startup. -/
theorem stop_arm {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high nativeSp : Nat} {saved : Nat → BitVec 64} {value : BitVec 64} {c : Config}
    (h : ArmInput L P s .STOP c pl cp sp high)
    (invocation : StopInvocation nativeSp saved (BitVec.ofNat 64 sp) c)
    (encoded : valWord pl s.accu = some value) :
    ∃ after, Plus c after ∧ StopReturnPost c nativeSp saved value (BitVec.ofNat 64 sp) after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have input : StopInput nativeSp saved value (BitVec.ofNat 64 sp) d := {
    toStopInvocation := invocation.frame_read dp.memory (dp.frame.frame _ (by decide))
    good := dp.good
    image := dp.image h.dispatch.image
    pc := dp.pc
    tick := dp.tick
    vmStack := (dp.frame.frame _ (by decide)).trans h.spReg
    value := (dp.frame.frame _ (by decide)).trans (represented_register h.accu encoded) }
  obtain ⟨count, after, run, post⟩ := stop_return input
  refine ⟨count, after, run, post.good, post.image, post.tick, post.pc,
    post.stack, post.value, post.registers, ?_, post.output.trans dp.frame.out⟩
  simpa only [stopLog, stopDepth, word, dp.memory] using post.memory

/-- STOP's bytecode halt is realized once the enclosing native exit path is supplied. -/
theorem stop_halt_arm {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high nativeSp : Nat} {saved : Nat → BitVec 64} {value : BitVec 64} {c : Config}
    (h : ArmInput L P s .STOP c pl cp sp high)
    (invocation : StopInvocation nativeSp saved (BitVec.ofNat 64 sp) c)
    (encoded : valWord pl s.accu = some value)
    (exit : StopExitContinuation c nativeSp saved value (BitVec.ofNat 64 sp) (bytesToString s.world.console)) :
    Halts c (bytesToString s.world.console) 0 := by
  obtain ⟨after, ⟨count, run⟩, post⟩ := stop_arm h invocation encoded
  exact Halts.of_steps run.toSteps (exit.resume after post)

/-- Consume the actual STOP semantic outcome, including its output world and exit code. -/
theorem stop_halt_step_arm {L : OCaml.Layout} {P : Prog} {s : St} {pl : Place} {cp : ChanPlace}
    {sp high nativeSp : Nat} {saved : Nat → BitVec 64} {value : BitVec 64} {c : Config}
    {e : Nat} {w : World}
    (h : ArmInput L P s .STOP c pl cp sp high)
    (invocation : StopInvocation nativeSp saved (BitVec.ofNat 64 sp) c)
    (encoded : valWord pl s.accu = some value)
    (exit : StopExitContinuation c nativeSp saved value (BitVec.ofNat 64 sp) (bytesToString s.world.console))
    (step : stepI P s ⟨.STOP, []⟩ = .halt e w) : Halts c (bytesToString w.console) e := by
  simp only [stepI, Res.halt.injEq] at step
  obtain ⟨rfl, rfl⟩ := step
  exact stop_halt_arm h invocation encoded exit

end OCaml.Vm.Sim
