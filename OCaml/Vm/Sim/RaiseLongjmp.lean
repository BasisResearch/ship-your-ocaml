import OCaml.Vm.Sim.RaiseRuntimeSuffix
import OCaml.Vm.Sim.RaiseRuntimeCalls
import OCaml.Vm.Sim.Longjmp
import OCaml.Vm.Sim.EffectFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Native exception publication retains the saved nonlocal-return environment. -/
structure RaiseLongjmpInput (domain value : BitVec 64) (buffer : Nat)
    (saved : Nat → BitVec 64) (c : Config) : Prop
    extends RaiseRuntimeSuffixInput domain (BitVec.ofNat 64 buffer) value c where
  savedFrame : JumpSavedFrame buffer saved c
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs,
    OutLRange (raiseBucketLog domain value) (buffer + Layout.jumpSaveOffset r) 8
  aligned : (saved 1).toNat % 4 = 0

/-- The native exception reaches its saved continuation with the exception published. -/
structure NativeRaisePost (log : List WEntry) (saved : Nat → BitVec 64)
    (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some (saved 1)
  registers : ∀ r ∈ Layout.jumpSavedRegs, gpr after r = some (saved r)
  result : gpr after 10 = some 1#64
  memory : after.σ.mem = writeLog before.σ.mem log
  frame : StepFrameOut ([Register.x1, Register.x10, Register.x11, Register.x13,
    Register.x14, Register.x15] ++ longjmpWrites) before.σ after.σ

abbrev RaiseLongjmpPost (domain value : BitVec 64) (saved : Nat → BitVec 64) (before : Config) :=
  NativeRaisePost (raiseBucketLog domain value) saved before

/-- Execute publication, the pinned JAL, and the complete longjmp callee. -/
theorem raise_longjmp {domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c : Config} (h : RaiseLongjmpInput domain value buffer saved c) :
    FnSummary 0x8000ce44#64 (fun start => start = c) (RaiseLongjmpPost domain value saved c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, prefixRun, publish⟩ := (raise_runtime_suffix h.toRaiseRuntimeSuffixInput).run c ⟨pc, rfl⟩
  have regs : GHolds middle.σ [(10, BitVec.ofNat 64 buffer), (11, 1#64)] :=
    ⟨publish.result, gholds_lookup _ publish.regs (by rfl), trivial⟩
  have call := call_registers_summary caml_raise_8000ce70_call_shape caml_raise_8000ce70_call_decode
    middle (caml_raise_8000ce70_call_pins publish.image) publish.good publish.image publish.tick publish.minstret
    [(10, BitVec.ofNat 64 buffer), (11, 1#64)] regs (by change KeysOK [10, 11]; decide)
    (by change ∀ n ∈ [10, 11], n ≠ 1; decide) (by rfl)
  obtain ⟨jumpStart, callRun, callPost⟩ := call.run middle ⟨publish.pc, rfl⟩
  have memory : jumpStart.σ.mem = writeLog c.σ.mem (raiseBucketLog domain value) :=
    callPost.memory.trans publish.memory
  have input : LongjmpInput buffer saved 1#64 jumpStart := {
    good := callPost.good, image := callPost.image, tick := callPost.tick
    frame := h.savedFrame.frame h.savedOutside memory
    bufferReg := callPost.result
    valueReg := gholds_lookup _ callPost.regs (by rfl)
    aligned := h.aligned }
  obtain ⟨after, jumpRun, jump⟩ := (longjmp_summary input).run jumpStart
    ⟨callPost.pc.trans (congrArg some caml_raise_8000ce70_call_target), rfl⟩
  refine ⟨after, prefixRun.trans (callRun.trans jumpRun), jump.good, jump.image, jump.tick,
    jump.pc, jump.registers, ?_, jump.memory.trans memory, ?_⟩
  · exact jump.value
  · exact ((publish.toEffectPost.nativeFrame.trans callPost.toEffectPost.nativeFrame).trans jump.frame).widenChecked (by decide)

end OCaml.Vm.Sim
