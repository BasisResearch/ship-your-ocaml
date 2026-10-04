import OCaml.Vm.Sim.RaisePending
import OCaml.Vm.Sim.RaiseLongjmp

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def raiseNativeLog (sp ra domain value : BitVec 64) : List WEntry :=
  raisePendingLog sp ra value ++ raiseBucketLog domain value

/-- Complete quiet native raising conditions, separated from VM data representation. -/
structure RaiseNativeInput (sp ra domain value : BitVec 64) (buffer : Nat)
    (saved : Nat → BitVec 64) (c : Config) : Prop where
  pending : RaisePendingInput sp ra value c
  jump : RaiseLongjmpInput domain value buffer saved c
  runtimeOutside : ∀ a ∈ [Layout.sym_Caml_state, (raiseExternal domain).toNat],
    OutLRange (raisePendingLog sp ra value) a 8
  savedOutside : ∀ r ∈ Layout.jumpSavedRegs,
    OutLRange (raisePendingLog sp ra value) (buffer + Layout.jumpSaveOffset r) 8

/-- The pending-call stores retain the later domain and saved-buffer observations. -/
theorem raise_native_jump_input {sp ra domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c middle : Config}
    (h : RaiseNativeInput sp ra domain value buffer saved c)
    (post : RaisePendingPost sp ra value c middle) : RaiseLongjmpInput domain value buffer saved middle := by
  have read : ∀ a ∈ [Layout.sym_Caml_state, (raiseExternal domain).toNat], word middle a = word c a := by
    intro a member
    rw [word, post.memory]
    exact bytesT_writeLog_out _ (h.runtimeOutside a member)
  refine {
    toRaiseRuntimeSuffixInput := {
      h.jump.toRaiseRuntimeSuffixInput with
      good := post.good, image := post.image, tick := post.tick, argument := post.result
      domainWord := (read _ (by simp)).trans h.jump.domainWord
      externalWord := (read _ (by simp)).trans h.jump.externalWord }
    savedFrame := h.jump.savedFrame.frame h.savedOutside post.memory
    savedOutside := h.jump.savedOutside
    aligned := h.jump.aligned }

/-- Complete caml_raise quiet path: saved caller, pending check, publication, JAL and longjmp. -/
theorem raise_native {sp ra domain value : BitVec 64} {buffer : Nat}
    {saved : Nat → BitVec 64} {c : Config} (h : RaiseNativeInput sp ra domain value buffer saved c) :
    FnSummary 0x8000ce20#64 (fun start => start = c)
      (NativeRaisePost (raiseNativeLog sp ra domain value) saved c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨middle, pendingRun, post⟩ := (raise_pending h.pending).run c ⟨pc, rfl⟩
  obtain ⟨after, jumpRun, jump⟩ := (raise_longjmp (raise_native_jump_input h post)).run middle ⟨post.pc, rfl⟩
  refine ⟨after, pendingRun.trans jumpRun, jump.good, jump.image, jump.tick, jump.pc,
    jump.registers, jump.result, ?_, ?_⟩
  · rw [jump.memory, post.memory, raiseNativeLog, writeLog_append]
  · exact (post.frame.trans jump.frame).widenChecked (by decide)

end OCaml.Vm.Sim
