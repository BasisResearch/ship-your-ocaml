import OCaml.Vm.Sim.DivisionZeroNative
import OCaml.Vm.Sim.DivintZero
import OCaml.Vm.Sim.ModintZero
import OCaml.Vm.Sim.SignedDivisionState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def divisionZeroEntry : DivisionKind → BitVec 64
  | .quotient => 0x80002d10#64
  | .remainder => 0x80002ce4#64

/-- Both generated zero selections expose the same memory/register frame. -/
theorem division_zero_select (kind : DivisionKind) {sp : BitVec 64} {c : Config}
    (h : DivisionZeroInput sp c) :
    FnSummary (divisionZeroEntry kind) (fun start => start = c) (DivisionZeroPost sp c) := by
  cases kind with
  | quotient => exact divint_zero h
  | remainder => exact modint_zero h

/-- The read-only zero branch preserves all later setup and runtime readiness. -/
theorem DivisionZeroNativeInput.after_select {code sp env domain nativeSp global value : BitVec 64}
    {buffer : Nat} {saved : Nat → BitVec 64} {c middle : Config}
    (h : DivisionZeroNativeInput code sp env domain nativeSp global value buffer saved c)
    (post : DivisionZeroPost sp c middle) :
    DivisionZeroNativeInput code sp env domain nativeSp global value buffer saved middle := by
  exact {
    setup := {
      h.setup with
      good := post.good, image := post.image, tick := post.tick
      codeReg := (post.frame.frame Register.x8 (by decide)).trans h.setup.codeReg
      stack := post.stack
      environment := (post.frame.frame Register.x25 (by decide)).trans h.setup.environment
      domainWord := by simpa only [word, post.memory] using h.setup.domainWord }
    nativeStack := (post.frame.frame Register.x2 (by decide)).trans h.nativeStack
    runtime := h.runtime.frame (log := []) post.memory (by intros; trivial) (by trivial) (by intros; trivial)
    wordsOutside := h.wordsOutside, pendingOutside := h.pendingOutside, savedOutside := h.savedOutside }

/-- Complete native DIVINT/MODINT zero path through the runtime raising chain. -/
theorem division_zero (kind : DivisionKind) {code sp env domain nativeSp global value : BitVec 64}
    {buffer : Nat} {saved : Nat → BitVec 64} {c : Config}
    (select : DivisionZeroInput sp c)
    (h : DivisionZeroNativeInput code sp env domain nativeSp global value buffer saved c) :
    FnSummary (divisionZeroEntry kind) (fun start => start = c)
      (NativeRaisePost (divisionZeroNativeLog code sp env domain nativeSp value) saved c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, selectRun, post⟩ := (division_zero_select kind select).run c ⟨pc, rfl⟩
  obtain ⟨after, raiseRun, raised⟩ := (division_zero_native (h.after_select post)).run middle ⟨post.pc, rfl⟩
  refine ⟨after, selectRun.trans raiseRun, raised.good, raised.image, raised.tick, raised.pc,
    raised.registers, raised.result, ?_, ?_⟩
  · simpa only [post.memory] using raised.memory
  · exact (post.frame.trans raised.frame).widenChecked (by decide)

end OCaml.Vm.Sim
