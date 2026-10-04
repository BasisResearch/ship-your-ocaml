import OCaml.Vm.Sim.RaiseZeroPrefix
import OCaml.Vm.Sim.RaiseZeroValue
import OCaml.Vm.Sim.RaiseZeroDivideCalls
import OCaml.Vm.Sim.CheckGlobalData
import OCaml.Vm.Sim.EffectFrame
import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The predefined exception and global block survive the helper's native frame save. -/
structure RaiseZeroSetupInput (sp ra global value : BitVec 64) (c : Config) : Prop where
  prologue : RaiseZeroPrefixInput sp ra c
  exceptionValue : RaiseZeroValueInput global value c
  globalBlock : global &&& 1#64 = 0#64
  outside : ∀ a ∈ [Layout.sym_caml_global_data, (raiseZeroField global).toNat], OutLRange (raiseZeroLog sp ra) a 8

/-- Zero-divisor setup reaches caml_raise's call with the predefined exception selected. -/
structure RaiseZeroSetupPost (sp ra value : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x8000d1f4#64
  stack : gpr after 2 = some (raiseZeroStack sp)
  result : gpr after 10 = some value
  memory : after.σ.mem = writeLog before.σ.mem (raiseZeroLog sp ra)
  frame : StepFrameOut ([Register.x1, Register.x2, Register.x10, Register.x15] ++ noiseRegs) before.σ after.σ

/-- Execute the zero-divisor frame save, global check call/return and exception load. -/
theorem raise_zero_setup {sp ra global value : BitVec 64} {c : Config}
    (h : RaiseZeroSetupInput sp ra global value c) :
    FnSummary 0x8000d1d4#64 (fun start => start = c) (RaiseZeroSetupPost sp ra value c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, saveRun, save⟩ := (raise_zero_prefix h.prologue).run c ⟨pc, rfl⟩
  have regs : GHolds middle.σ [(2, raiseZeroStack sp), (10, BitVec.ofNat 64 Layout.raiseZeroMessage)] :=
    ⟨gholds_lookup _ save.regs (by rfl), save.result, trivial⟩
  have call := call_registers_summary caml_raise_zero_divide_8000d1e4_call_shape caml_raise_zero_divide_8000d1e4_call_decode
    middle (caml_raise_zero_divide_8000d1e4_call_pins save.image) save.good save.image save.tick save.minstret
    [(2, raiseZeroStack sp), (10, BitVec.ofNat 64 Layout.raiseZeroMessage)] regs
    (by change KeysOK [2, 10]; decide) (by change ∀ n ∈ [2, 10], n ≠ 1; decide) (by rfl)
  obtain ⟨checkStart, callRun, called⟩ := call.run middle ⟨save.pc, rfl⟩
  have checkMemory : checkStart.σ.mem = writeLog c.σ.mem (raiseZeroLog sp ra) := called.memory.trans save.memory
  have globalWord : word checkStart Layout.sym_caml_global_data = global := by
    rw [word, checkMemory, bytesT_writeLog_out _ (h.outside _ (by simp))]
    exact h.exceptionValue.globalWord
  have checkInput : CheckGlobalDataInput 0x8000d1e8#64 checkStart := {
    good := called.good, image := called.image, tick := called.tick
    returnReg := gholds_lookup _ called.regs (by rfl), aligned := by decide
    globalBlock := by rw [globalWord]; exact h.globalBlock }
  obtain ⟨loadStart, checkRun, checked⟩ := (check_global_data_summary checkInput).run checkStart
    ⟨called.pc.trans (congrArg some caml_raise_zero_divide_8000d1e4_call_target), rfl⟩
  have loadMemory : loadStart.σ.mem = writeLog c.σ.mem (raiseZeroLog sp ra) := checked.memory.trans checkMemory
  have read : ∀ a ∈ [Layout.sym_caml_global_data, (raiseZeroField global).toNat], word loadStart a = word c a := by
    intro a member
    rw [word, loadMemory]
    exact bytesT_writeLog_out _ (h.outside a member)
  have valueInput : RaiseZeroValueInput global value loadStart := {
    good := checked.good, image := checked.image, tick := checked.tick
    globalWord := (read _ (by simp)).trans h.exceptionValue.globalWord
    fieldRead := h.exceptionValue.fieldRead
    fieldWord := (read _ (by simp)).trans h.exceptionValue.fieldWord }
  obtain ⟨after, loadRun, loaded⟩ := (raise_zero_value valueInput).run loadStart ⟨checked.pc, rfl⟩
  have loadedFrame := loaded.toEffectPost.nativeFrame
  refine ⟨after, saveRun.trans (callRun.trans (checkRun.trans loadRun)), loaded.good, loaded.image, loaded.tick,
    loaded.pc, ?_, loaded.result, loaded.memory.trans loadMemory, ?_⟩
  · exact (loadedFrame.frame Register.x2 (by decide)).trans
      ((checked.frame.frame Register.x2 (by decide)).trans (gholds_lookup (n := 2) _ called.regs (by rfl)))
  · exact (((save.toEffectPost.nativeFrame.trans called.toEffectPost.nativeFrame).trans checked.frame).trans loadedFrame).widenChecked (by decide)

end OCaml.Vm.Sim
