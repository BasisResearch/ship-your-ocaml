import OCaml.Vm.Boot.Startup.SecureGetenv
import OCaml.Vm.Boot.Startup.Getenv
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def secureEnvLog (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  secureLog sp ra s0 s1 ++ getenvFullLog sp ra s1 s2 s3 s4 s5 s6

def secureEnvRegs (sp ra s0 s1 s2 s3 s4 s5 s6 name : BitVec 64) (count : Nat) : GRegs :=
  getenvRegs sp ra s1 s2 s3 s4 s5 s6 name count ++ [(8, s0)]

theorem secureEnvLog_inside {sp ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (secureEnvLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
  apply log_in_append
  · apply log_in_larger_window (secure_log_inside (sp := sp) (ra := ra) (s0 := s0) (s1 := s1)
      (frame.resize (small := 32) (by decide) (by decide)))
    · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  · exact getenvFullLog_inside frame

/-- Full bare-metal caml_secure_getenv, including getenv and both native search
frames. Equal identities and an empty environment produce a null return. -/
theorem secure_getenv_empty (c : Config) (sp name env ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) (cs : List Char)
    (h : GetenvInput sp name env ra s1 s2 s3 s4 s5 s6 cs c) (saved0 : gprGet c.σ 8 = some s0) :
    FnSummary 0x800256e4#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (secureEnvLog sp ra s0 s1 s2 s3 s4 s5 s6) c ra 0#64
        (secureEnvRegs sp ra s0 s1 s2 s3 s4 s5 s6 name cs.length)) := by
  have outer := h.frame.resize (small := 32) (by decide) (by decide)
  have baseOrder : nativeFrameBase sp 112 ≤ nativeFrameBase sp 32 := by unfold nativeFrameBase; omega
  have regs : GHolds c.σ (secureInput sp name ra s0 s1) :=
    ⟨gholds_lookup (n := 2) _ h.regs (by rfl), saved0, gholds_lookup (n := 9) _ h.saved (by rfl), h.raReg,
      gholds_lookup (n := 10) _ h.regs (by rfl), trivial⟩
  apply summary_bind (secure_getenv_to_getenv c sp name ra s0 s1 h.toLeafInput regs outer) (fun _ post => post.pc)
  intro mid prepared
  have stable : GHolds mid.σ [(18, s2), (19, s3), (20, s4), (21, s5), (22, s6)] :=
    holds_frame_ne prepared.frame h.saved.2
      (by simp only [keysG]; decide) (by simp only [keysG]; decide) (by simp only [keysG]; decide)
  have input : GetenvInput sp name env ra s1 s2 s3 s4 s5 s6 cs mid := {
    toLeafInput := prepared.leaf (by rfl) h.aligned
    regs := holds_project prepared.regs (by simp [getenvPrefixInput, secureTailRegs, lookupG])
    saved := ⟨gholds_lookup (n := 9) _ prepared.regs (by rfl), stable⟩
    toEmptyEnvironment := h.toEmptyEnvironment.stack_log
      (log_in_larger_window (secure_log_inside outer) baseOrder (Nat.le_refl _)) prepared.memory
    data := h.data.stack_log (Nat.le_trans h.nameBelow baseOrder) (secure_log_inside outer) prepared.memory
    positive := h.positive
    nameBelow := h.nameBelow }
  apply (getenv_empty mid sp name env ra s1 s2 s3 s4 s5 s6 cs input).weaken (fun _ eq => eq)
  intro after post
  have effects := prepared.toEffectPost.trans post.toEffectPost
  refine ⟨?_, ?_⟩
  · have widened := effects.widen (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
    refine ⟨widened.good, widened.image, widened.minstret, widened.tick, widened.pc,
      widened.result, ?_, widened.output, widened.frame⟩
    rw [post.memory, prepared.memory, secureEnvLog, writeLog_append]
  · apply (gholds_append _ _).mpr
    exact ⟨post.regs, (post.frame .x8 (by decide) (by decide)).trans (gholds_lookup (n := 8) _ prepared.regs (by rfl)), trivial⟩
end OCaml.Vm.Boot.Startup
