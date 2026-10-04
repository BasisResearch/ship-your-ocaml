import OCaml.Vm.Sim.DivisionZeroSetup
import OCaml.Vm.Sim.RaiseZero

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def divisionZeroNativeLog (code sp env domain nativeSp value : BitVec 64) : List WEntry :=
  divisionZeroSetupLog code sp env domain ++ raiseZeroFullLog nativeSp 0x80003cb0#64 domain value

/-- Memory readiness at the common interpreter exception setup. -/
structure DivisionZeroNativeInput (code sp env domain nativeSp global value : BitVec 64)
    (buffer : Nat) (saved : Nat → BitVec 64) (c : Config) : Prop where
  setup : DivisionZeroSetupInput code sp env domain c
  nativeStack : gpr c 2 = some nativeSp
  runtime : RaiseZeroMemory nativeSp 0x80003cb0#64 global domain value buffer saved c
  wordsOutside : ∀ a ∈ raiseZeroMemoryWords global domain, OutLRange (divisionZeroSetupLog code sp env domain) a 8
  pendingOutside : OutLRange (divisionZeroSetupLog code sp env domain) Layout.sym_caml_something_to_do 4
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs, OutLRange (divisionZeroSetupLog code sp env domain) (buffer + Layout.jumpSaveOffset r) 8

/-- Execute the interpreter setup and complete zero-divisor helper to the saved continuation. -/
theorem division_zero_native {code sp env domain nativeSp global value : BitVec 64}
    {buffer : Nat} {saved : Nat → BitVec 64} {c : Config}
    (h : DivisionZeroNativeInput code sp env domain nativeSp global value buffer saved c) :
    FnSummary 0x80003c90#64 (fun start => start = c)
      (NativeRaisePost (divisionZeroNativeLog code sp env domain nativeSp value) saved c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, setupRun, setup⟩ := (division_zero_setup h.setup).run c ⟨pc, rfl⟩
  have ready := h.runtime.frame setup.memory h.wordsOutside h.pendingOutside h.savedOutside
  have input : RaiseZeroInput nativeSp 0x80003cb0#64 global domain value buffer saved middle := {
    toRaiseZeroMemory := ready
    good := setup.good, image := setup.image, tick := setup.tick
    stack := (setup.frame.frame Register.x2 (by decide)).trans h.nativeStack
    returnReg := setup.returnReg }
  obtain ⟨after, raiseRun, raised⟩ := (raise_zero input).run middle ⟨setup.pc, rfl⟩
  refine ⟨after, setupRun.trans raiseRun, raised.good, raised.image, raised.tick, raised.pc,
    raised.registers, raised.result, ?_, ?_⟩
  · rw [raised.memory, setup.memory, divisionZeroNativeLog, writeLog_append]
  · exact (setup.frame.trans raised.frame).widenChecked (by decide)

end OCaml.Vm.Sim
