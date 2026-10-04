import OCaml.Vm.Sim.RaiseZeroSetup
import OCaml.Vm.Sim.RaiseMemory

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def raiseZeroFullLog (sp ra domain value : BitVec 64) : List WEntry :=
  raiseZeroLog sp ra ++ raiseNativeLog (raiseZeroStack sp) 0x8000d1f8#64 domain value

/-- Scalar quiet-runtime readiness for the full zero-divisor raising helper. -/
structure RaiseZeroInput (sp ra global domain value : BitVec 64) (buffer : Nat)
    (saved : Nat → BitVec 64) (c : Config) : Prop where
  setup : RaiseZeroSetupInput sp ra global value c
  native : RaiseNativeMemory (raiseZeroStack sp) 0x8000d1f8#64 domain value buffer saved c
  wordsOutside : ∀ a ∈ raiseMemoryWords domain, OutLRange (raiseZeroLog sp ra) a 8
  pendingOutside : OutLRange (raiseZeroLog sp ra) Layout.sym_caml_something_to_do 4
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs, OutLRange (raiseZeroLog sp ra) (buffer + Layout.jumpSaveOffset r) 8

/-- Complete caml_raise_zero_divide execution, including the check and raising callees. -/
theorem raise_zero {sp ra global domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c : Config} (h : RaiseZeroInput sp ra global domain value buffer saved c) :
    FnSummary 0x8000d1d4#64 (fun start => start = c)
      (NativeRaisePost (raiseZeroFullLog sp ra domain value) saved c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, setupRun, setup⟩ := (raise_zero_setup h.setup).run c ⟨pc, rfl⟩
  have regs : GHolds middle.σ [(2, raiseZeroStack sp), (10, value)] := ⟨setup.stack, setup.result, trivial⟩
  have call := call_registers_summary caml_raise_zero_divide_8000d1f4_call_shape caml_raise_zero_divide_8000d1f4_call_decode
    middle (caml_raise_zero_divide_8000d1f4_call_pins setup.image) setup.good setup.image setup.tick setup.good.minstret
    [(2, raiseZeroStack sp), (10, value)] regs
    (by change KeysOK [2, 10]; decide) (by change ∀ n ∈ [2, 10], n ≠ 1; decide) (by rfl)
  obtain ⟨raiseStart, callRun, called⟩ := call.run middle ⟨setup.pc, rfl⟩
  have memory : raiseStart.σ.mem = writeLog c.σ.mem (raiseZeroLog sp ra) := called.memory.trans setup.memory
  have ready := h.native.frame memory h.wordsOutside h.pendingOutside h.savedOutside
  have input := ready.input called.good called.image called.tick
    (gholds_lookup _ called.regs (by rfl)) (gholds_lookup _ called.regs (by rfl)) called.result
  obtain ⟨after, raiseRun, raised⟩ := (raise_native input).run raiseStart
    ⟨called.pc.trans (congrArg some caml_raise_zero_divide_8000d1f4_call_target), rfl⟩
  refine ⟨after, setupRun.trans (callRun.trans raiseRun), raised.good, raised.image, raised.tick,
    raised.pc, raised.registers, raised.result, ?_, ?_⟩
  · rw [raised.memory, memory, raiseZeroFullLog, writeLog_append]
  · exact ((setup.frame.trans called.toEffectPost.nativeFrame).trans raised.frame).widenChecked (by decide)

end OCaml.Vm.Sim
