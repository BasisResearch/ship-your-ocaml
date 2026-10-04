import OCaml.Vm.Sim.RaiseNative

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Runtime memory readiness independent of the caller's current ABI registers. -/
structure RaiseNativeMemory (sp ra domain value : BitVec 64) (buffer : Nat)
    (saved : Nat → BitVec 64) (c : Config) : Prop where
  prologue : RaiseRuntimePrefixMemory sp ra c
  pending : RaisePendingMemory sp ra value c
  publish : RaiseRuntimeSuffixMemory domain (BitVec.ofNat 64 buffer) value c
  jump : RaiseLongjmpMemory domain value buffer saved c
  runtimeOutside : ∀ a ∈ [Layout.sym_Caml_state, (raiseExternal domain).toNat],
    OutLRange (raisePendingLog sp ra value) a 8
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs,
    OutLRange (raisePendingLog sp ra value) (buffer + Layout.jumpSaveOffset r) 8

/-- The real caller supplies the ABI registers only when it reaches caml_raise. -/
theorem RaiseNativeMemory.input {sp ra domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c : Config} (h : RaiseNativeMemory sp ra domain value buffer saved c)
    (good : GoodState c.σ) (image : ExecutableImage c) (tick : c.tick < 2)
    (stack : gpr c 2 = some sp) (returnReg : gpr c 1 = some ra) (argument : gpr c 10 = some value) :
    RaiseNativeInput sp ra domain value buffer saved c := {
  pending := {
    toRaiseRuntimePrefixInput := {
      toRaiseRuntimePrefixMemory := h.prologue
      good := good, image := image, tick := tick, stack := stack, returnReg := returnReg, argument := argument }
    toRaisePendingMemory := h.pending }
  jump := {
    toRaiseRuntimeSuffixInput := {
      toRaiseRuntimeSuffixMemory := h.publish
      good := good, image := image, tick := tick, argument := argument }
    toRaiseLongjmpMemory := h.jump }
  runtimeOutside := h.runtimeOutside, savedOutside := h.savedOutside }

def raiseMemoryWords (domain : BitVec 64) : List Nat :=
  [Layout.sym_caml_channel_mutex_unlock_exn, Layout.sym_Caml_state, (raiseExternal domain).toNat]

/-- All memory readiness survives a caller log disjoint from the observed runtime words. -/
theorem RaiseNativeMemory.frame {sp ra domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c after : Config} {log : List WEntry}
    (h : RaiseNativeMemory sp ra domain value buffer saved c)
    (memory : after.σ.mem = writeLog c.σ.mem log)
    (wordsOutside : ∀ a ∈ raiseMemoryWords domain, OutLRange log a 8)
    (pendingOutside : OutLRange log Layout.sym_caml_something_to_do 4)
    (savedOutside : ∀ r ∈ Layout.jumpSavedRegs, OutLRange log (buffer + Layout.jumpSaveOffset r) 8) :
    RaiseNativeMemory sp ra domain value buffer saved after := by
  have read : ∀ a ∈ raiseMemoryWords domain, word after a = word c a := by
    intro a member
    rw [word, memory]
    exact bytesT_writeLog_out _ (wordsOutside a member)
  have pending : word32 after Layout.sym_caml_something_to_do = 0#32 := by
    rw [word32, memory, bytesT_writeLog_out _ pendingOutside]
    exact h.pending.pending
  exact {
    prologue := { h.prologue with hook := (read _ (by simp [raiseMemoryWords])).trans h.prologue.hook }
    pending := { h.pending with pending := pending }
    publish := { h.publish with
      domainWord := (read _ (by simp [raiseMemoryWords])).trans h.publish.domainWord
      externalWord := (read _ (by simp [raiseMemoryWords])).trans h.publish.externalWord }
    jump := { h.jump with savedFrame := h.jump.savedFrame.frame savedOutside memory }
    runtimeOutside := h.runtimeOutside, savedOutside := h.savedOutside }

end OCaml.Vm.Sim
