import OCaml.Vm.Boot.Startup.ParameterPrefixCallInterface
import OCaml.Vm.Boot.Startup.ParameterFallbackCallInterface
import OCaml.Vm.Boot.Startup.ParameterNameFrame
import OCaml.Vm.Boot.Startup.SecureEnvReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def parameterCall (fallback : Bool) : CallInstr := if fallback then jal_80004744_call else jal_80004530_call

theorem parameterCall_shape (fallback : Bool) : CallShape (parameterCall fallback) := by
  cases fallback
  · exact jal_80004530_call_shape
  · exact jal_80004744_call_shape

theorem parameterCall_decode (fallback : Bool) : CallDecode (parameterCall fallback) := by
  cases fallback
  · exact jal_80004530_call_decode
  · exact jal_80004744_call_decode

theorem parameterCall_pins (fallback : Bool) {c : Config} (image : ExecutableImage c) : CallPins (parameterCall fallback) c := by
  cases fallback
  · exact jal_80004530_call_pins image
  · exact jal_80004744_call_pins image

def parameterQueryRegs (fallback : Bool) (sp s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  [(10, parameterName fallback), (2, sp), (8, s0)] ++ getenvSavedRegs s1 s2 s3 s4 s5 s6

structure ParameterQueryInput (fallback : Bool) (sp env ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  regs : GHolds c.σ (parameterQueryRegs fallback sp s0 s1 s2 s3 s4 s5 s6)
  frame : NativeFrame sp 112
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  nonnull : env ≠ 0#64
  envWindow : ReadWindow env 8
  empty : bytesT c.σ.mem env.toNat 8 = 0#64
  envBelow : env.toNat + 8 ≤ nativeFrameBase sp 112

/-- Both parameter-query sites call the complete secure getenv summary; their
literal name representation is supplied by the pinned read-only image. -/
theorem parameter_query (fallback : Bool) (c : Config) (sp env ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (h : ParameterQueryInput fallback sp env ra s0 s1 s2 s3 s4 s5 s6 c) :
    FnSummary (parameterCall fallback).pc (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (secureEnvLog sp (parameterCall fallback).link s0 s1 s2 s3 s4 s5 s6) c (parameterCall fallback).link 0#64
        (secureEnvRegs sp (parameterCall fallback).link s0 s1 s2 s3 s4 s5 s6
          (parameterName fallback) (parameterChars fallback).length)) := by
  have target : (parameterCall fallback).target = 0x800256e4#64 := by cases fallback <;> decide
  have linkAligned : (parameterCall fallback).link.toNat % 4 = 0 := by cases fallback <;> decide
  have call := call_registers_summary (parameterCall_shape fallback) (parameterCall_decode fallback) c
    (parameterCall_pins fallback h.image) h.good h.image h.tick h.minstret _ h.regs
    (by simp only [parameterQueryRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [KeysAvoidRa, parameterQueryRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide) (by rfl)
  apply summary_bind call (fun _ post => post.pc.trans (congrArg some target))
  intro mid called
  have input : GetenvInput sp (parameterName fallback) env (parameterCall fallback).link s1 s2 s3 s4 s5 s6
      (parameterChars fallback) mid := {
    toLeafInput := called.leaf (by rfl) linkAligned
    regs := holds_project called.regs (by simp [getenvPrefixInput, parameterQueryRegs, lookupG])
    saved := holds_project called.regs (by simp [getenvSavedRegs, parameterQueryRegs, lookupG])
    frame := h.frame
    data := parameter_name fallback called.image
    positive := parameter_name_positive fallback
    nameBelow := parameter_name_below fallback h.frame
    environment := by rw [called.memory]; exact h.environment
    nonnull := h.nonnull
    envWindow := h.envWindow
    empty := by rw [called.memory]; exact h.empty
    envBelow := h.envBelow }
  apply (secure_getenv_empty mid sp (parameterName fallback) env _ s0 s1 s2 s3 s4 s5 s6 _ input
    (gholds_lookup (n := 8) _ called.regs (by rfl))).weaken (fun _ eq => eq)
  intro after post
  have effects := called.toEffectPost.trans post.toEffectPost
  have widened := effects.widen (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨⟨widened.good, widened.image, widened.minstret, widened.tick, widened.pc,
    widened.result, ?_, widened.output, widened.frame⟩, post.regs⟩
  rw [post.memory, called.memory]
end OCaml.Vm.Boot.Startup
