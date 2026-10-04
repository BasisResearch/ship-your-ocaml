import OCaml.Vm.Boot.Startup.SecureGetenv
import OCaml.Vm.Boot.Startup.GetenvPresentReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def securePresentLog (sp ra s0 s1 s2 s3 s4 s5 s6 pointer : BitVec 64) : List WEntry :=
  secureLog sp ra s0 s1 ++ getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 pointer

theorem securePresentLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6 pointer} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (securePresentLog sp ra s0 s1 s2 s3 s4 s5 s6 pointer) := by
  apply log_in_append
  · apply log_in_larger_window (secure_log_inside (sp := sp) (ra := ra) (s0 := s0) (s1 := s1)
      (frame.resize (small := 32) (by decide) (by decide)))
    · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  · exact getenvPresentLog_inside frame

/-- Complete caml_secure_getenv for a matching first environment entry. -/
theorem secure_getenv_present (c : Config) (sp env entry name ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (byte : Nat → BitVec 8)
    (h : GetenvPresentInput sp env entry name ra s0 s1 s2 s3 s4 s5 s6 cs byte c) :
    FnSummary 0x800256e4#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (securePresentLog sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry cs.length)) c ra (nameCursor entry cs.length + 1#64)
        (getenvPresentRegs sp ra s0 s1 s2 s3 s4 s5 s6 env entry name cs.length)) := by
  have outer := h.frame.resize (small := 32) (by decide) (by decide)
  have baseOrder : nativeFrameBase sp 112 ≤ nativeFrameBase sp 32 := by unfold nativeFrameBase; omega
  have regs : GHolds c.σ (secureInput sp name ra s0 s1) :=
    ⟨gholds_lookup (n := 2) _ h.regs (by rfl), h.saved0, gholds_lookup (n := 9) _ h.saved (by rfl), h.raReg,
      gholds_lookup (n := 10) _ h.regs (by rfl), trivial⟩
  apply summary_bind (secure_getenv_to_getenv c sp name ra s0 s1 h.toLeafInput regs outer) (fun _ post => post.pc)
  intro mid prepared
  have inside : LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (secureLog sp ra s0 s1) :=
    log_in_larger_window (secure_log_inside outer) baseOrder (Nat.le_refl _)
  have stable : GHolds mid.σ [(18, s2), (19, s3), (20, s4), (21, s5), (22, s6)] :=
    holds_frame_ne prepared.frame h.saved.2
      (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by simp only [keysG]; decide)
  have input : GetenvPresentInput sp env entry name ra s0 s1 s2 s3 s4 s5 s6 cs byte mid := {
    toLeafInput := prepared.leaf (by rfl) h.aligned
    frame := h.frame
    regs := holds_project prepared.regs (by simp [getenvPrefixInput, secureTailRegs, lookupG])
    saved := ⟨gholds_lookup (n := 9) _ prepared.regs (by rfl), stable⟩
    saved0 := gholds_lookup (n := 8) _ prepared.regs (by rfl)
    query := h.query.stack_log h.nameBelow inside prepared.memory
    nameBelow := h.nameBelow
    environment := by
      rw [prepared.memory, native_log_read_below c.σ.mem inside ?_]
      · exact h.environment
      · have lower := h.frame.lower
        have global : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
        unfold nativeFrameBase
        omega
    envNonzero := h.envNonzero
    search := h.search.stack_log (by rw [h.frame.nested_base (front := 32) (size := 80) (by decide)]; exact inside) prepared.memory }
  apply (getenv_present mid sp env entry name ra s0 s1 s2 s3 s4 s5 s6 cs byte input).weaken (fun _ eq => eq)
  intro after post
  have effects := (prepared.toEffectPost.trans post.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨⟨effects.good, effects.image, effects.minstret, effects.tick, effects.pc,
    effects.result, ?_, effects.output, effects.frame⟩, post.regs⟩
  rw [post.memory, prepared.memory, securePresentLog, writeLog_append]
end OCaml.Vm.Boot.Startup
