import OCaml.Vm.Sim.RaiseZeroSetup
import OCaml.Vm.Sim.RaiseMemory

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Zero-helper memory readiness before the caller supplies its native registers. -/
structure RaiseZeroSetupMemory (sp ra global value : BitVec 64) (c : Config) : Prop where
  prologue : RaiseZeroPrefixMemory sp ra
  exceptionValue : RaiseZeroValueMemory global value c
  globalBlock : global &&& 1#64 = 0#64
  outside : ∀ a ∈ [Layout.sym_caml_global_data, (raiseZeroField global).toNat], OutLRange (raiseZeroLog sp ra) a 8

/-- Attach actual entry registers to the reusable memory predicate. -/
theorem RaiseZeroSetupMemory.input {sp ra global value : BitVec 64} {c : Config}
    (h : RaiseZeroSetupMemory sp ra global value c) (good : GoodState c.σ)
    (image : ExecutableImage c) (tick : c.tick < 2)
    (stack : gpr c 2 = some sp) (returnReg : gpr c 1 = some ra) : RaiseZeroSetupInput sp ra global value c := {
  prologue := {
    toRaiseZeroPrefixMemory := h.prologue
    good := good, image := image, tick := tick, stack := stack, returnReg := returnReg }
  exceptionValue := { toRaiseZeroValueMemory := h.exceptionValue, good := good, image := image, tick := tick }
  globalBlock := h.globalBlock, outside := h.outside }

/-- Complete zero-helper memory readiness, independent of ABI entry facts. -/
structure RaiseZeroMemory (sp ra global domain value : BitVec 64) (buffer : Nat)
    (saved : Nat → BitVec 64) (c : Config) : Prop where
  setup : RaiseZeroSetupMemory sp ra global value c
  native : RaiseNativeMemory (raiseZeroStack sp) 0x8000d1f8#64 domain value buffer saved c
  wordsOutside : ∀ a ∈ raiseMemoryWords domain, OutLRange (raiseZeroLog sp ra) a 8
  pendingOutside : OutLRange (raiseZeroLog sp ra) Layout.sym_caml_something_to_do 4
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs, OutLRange (raiseZeroLog sp ra) (buffer + Layout.jumpSaveOffset r) 8

def raiseZeroMemoryWords (global domain : BitVec 64) : List Nat :=
  [Layout.sym_caml_global_data, (raiseZeroField global).toNat] ++ raiseMemoryWords domain

/-- Interpreter temporary-frame stores retain the complete zero-helper memory predicate. -/
theorem RaiseZeroMemory.frame {sp ra global domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c after : Config} {log : List WEntry}
    (h : RaiseZeroMemory sp ra global domain value buffer saved c)
    (memory : after.σ.mem = writeLog c.σ.mem log)
    (wordsOutside : ∀ a ∈ raiseZeroMemoryWords global domain, OutLRange log a 8)
    (pendingOutside : OutLRange log Layout.sym_caml_something_to_do 4)
    (savedOutside : ∀ r ∈ Layout.jumpSavedRegs, OutLRange log (buffer + Layout.jumpSaveOffset r) 8) :
    RaiseZeroMemory sp ra global domain value buffer saved after := by
  have read : ∀ a ∈ [Layout.sym_caml_global_data, (raiseZeroField global).toNat], word after a = word c a := by
    intro a member
    rw [word, memory]
    exact bytesT_writeLog_out _ (wordsOutside _ (List.mem_append_left _ member))
  exact {
    setup := { h.setup with exceptionValue := { h.setup.exceptionValue with
      globalWord := (read _ (by simp)).trans h.setup.exceptionValue.globalWord
      fieldWord := (read _ (by simp)).trans h.setup.exceptionValue.fieldWord } }
    native := h.native.frame memory (fun a member => wordsOutside a (List.mem_append_right _ member)) pendingOutside savedOutside
    wordsOutside := h.wordsOutside, pendingOutside := h.pendingOutside, savedOutside := h.savedOutside }

end OCaml.Vm.Sim
