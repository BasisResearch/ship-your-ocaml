import OCaml.Vm.Sim.RaiseRuntimePrefix
import OCaml.Vm.Sim.RaiseRuntimeCalls
import OCaml.Vm.Sim.PendingRoot
import OCaml.Vm.Sim.EffectFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def raisePendingLog (sp ra value : BitVec 64) : List WEntry :=
  raiseRuntimeLog sp ra ++ pendingRootLog (raiseRuntimeStack sp) 0x8000ce44#64 value

/-- Static write geometry and the preserved pending flag select the helper's fast path. -/
structure RaisePendingInput (sp ra value : BitVec 64) (c : Config) : Prop
    extends RaiseRuntimePrefixInput sp ra value c where
  pending : word32 c Layout.sym_caml_something_to_do = 0#32
  pendingOutside : OutLRange (raiseRuntimeLog sp ra) Layout.sym_caml_something_to_do 4
  pendingRaWrite : WriteWindow (pendingRootRa (raiseRuntimeStack sp)) 8
  pendingValueWrite : WriteWindow (pendingRootValue (raiseRuntimeStack sp)) 8
  pendingRaOutside : OutLRange [((pendingRootValue (raiseRuntimeStack sp)).toNat, 8, value)]
    (pendingRootRa (raiseRuntimeStack sp)).toNat 8
  pendingImageOutside : ImageOutside (pendingRootLog (raiseRuntimeStack sp) 0x8000ce44#64 value)

/-- The native raise frame remains installed after the root-preserving pending check. -/
structure RaisePendingPost (sp ra value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x8000ce44#64
  stack : gpr after 2 = some (raiseRuntimeStack sp)
  result : gpr after 10 = some value
  memory : after.σ.mem = writeLog before.σ.mem (raisePendingLog sp ra value)
  frame : StepFrameOut ([Register.x1, Register.x2, Register.x15] ++ noiseRegs) before.σ after.σ

/-- Execute the disabled-hook prefix, its actual call, and the no-pending return. -/
theorem raise_pending {sp ra value : BitVec 64} {c : Config} (h : RaisePendingInput sp ra value c) :
    FnSummary 0x8000ce20#64 (fun start => start = c) (RaisePendingPost sp ra value c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, saveRun, save⟩ := (raise_runtime_prefix h.toRaiseRuntimePrefixInput).run c ⟨pc, rfl⟩
  have regs : GHolds middle.σ [(2, raiseRuntimeStack sp), (10, value)] :=
    ⟨gholds_lookup _ save.regs (by rfl), save.result, trivial⟩
  have call := call_registers_summary caml_raise_8000ce40_call_shape caml_raise_8000ce40_call_decode
    middle (caml_raise_8000ce40_call_pins save.image) save.good save.image save.tick save.minstret
    [(2, raiseRuntimeStack sp), (10, value)] regs (by change KeysOK [2, 10]; decide)
    (by change ∀ n ∈ [2, 10], n ≠ 1; decide) (by rfl)
  obtain ⟨pendingStart, callRun, callPost⟩ := call.run middle ⟨save.pc, rfl⟩
  have memory : pendingStart.σ.mem = writeLog c.σ.mem (raiseRuntimeLog sp ra) := callPost.memory.trans save.memory
  have pending : word32 pendingStart Layout.sym_caml_something_to_do = 0#32 := by
    rw [word32, memory, bytesT_writeLog_out _ h.pendingOutside]
    exact h.pending
  have input : PendingRootInput (raiseRuntimeStack sp) 0x8000ce44#64 value pendingStart := {
    good := callPost.good, image := callPost.image, tick := callPost.tick
    stack := gholds_lookup _ callPost.regs (by rfl)
    returnReg := gholds_lookup _ callPost.regs (by rfl)
    argument := callPost.result, aligned := by decide
    pending := pending, raWrite := h.pendingRaWrite, valueWrite := h.pendingValueWrite
    raOutside := h.pendingRaOutside, imageOutside := h.pendingImageOutside }
  obtain ⟨after, pendingRun, post⟩ := (pending_root_summary input).run pendingStart
    ⟨callPost.pc.trans (congrArg some caml_raise_8000ce40_call_target), rfl⟩
  refine ⟨after, saveRun.trans (callRun.trans pendingRun), post.good, post.image, post.tick,
    post.pc, post.stack, post.result, ?_, ?_⟩
  · rw [post.memory, memory, raisePendingLog, writeLog_append]
  · exact ((save.toEffectPost.nativeFrame.trans callPost.toEffectPost.nativeFrame).trans post.frame).widenChecked (by decide)

end OCaml.Vm.Sim
