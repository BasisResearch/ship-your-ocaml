import OCaml.Vm.Sim.ReentryQuiet

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Native nonlocal return always takes the nonzero setjmp branch. -/
theorem longjmpValue_nonzero (value : BitVec 64) : longjmpValue value ≠ 0#64 := by
  by_cases zero : value = 0#64
  · simp only [longjmpValue, if_pos zero]; decide
  · simpa only [longjmpValue, if_neg zero] using zero

/-- Combined nonlocal return retains the restored ABI state except re-entry scratch registers. -/
structure NonlocalReentryPost (nativeSp : Nat) (before after : Config) : Prop
    extends ReentryControl nativeSp before after where
  frame : StepFrameOut (longjmpWrites ++ [Register.x8, Register.x12, Register.x13,
    Register.x14, Register.x15, Register.x9, Register.x21] ++ noiseRegs) before.σ after.σ

/-- Compose the checked longjmp function and actual quiet interpreter continuation.
The saved invocation identifies the return PC/stack; the primitive supplies memory readiness. -/
theorem longjmp_reentry {buffer nativeSp : Nat} {saved : Nat → BitVec 64}
    {value : BitVec 64} {c : Config}
    (h : LongjmpInput buffer saved value c) (ready : ReentryMemory nativeSp c)
    (returnPc : saved 1 = 0x80001e80#64) (returnSp : saved 2 = BitVec.ofNat 64 nativeSp) :
    FnSummary (0x80042c8c#64) (fun start => start = c) (NonlocalReentryPost nativeSp c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, jumpRun, jump⟩ := (longjmp_summary h).run c ⟨pc, rfl⟩
  have input : ReentryQuietInput nativeSp (longjmpValue value) middle := {
    toReentryMemory := ready.frame jump.memory
    good := jump.good, image := jump.image, tick := jump.tick
    pc := jump.pc.trans (congrArg some returnPc)
    stack := (jump.registers 2 (by decide)).trans (congrArg some returnSp)
    resultReg := jump.value, nonzero := longjmpValue_nonzero value
    s10 := by rw [jump.registers 26 (by decide)]; rfl }
  obtain ⟨count, after, run, post⟩ := reentry_quiet input
  refine ⟨after, jumpRun.trans run.toSteps,
    post.toReentryControl.before_read jump.memory jump.frame.out (jump.frame.frame _ (by decide)), ?_⟩
  exact (jump.frame.trans post.frame).widenChecked (by decide)

end OCaml.Vm.Sim
