import OCaml.Vm.Boot.Startup.SecurePresentReady
import OCaml.Vm.Boot.Startup.ParameterQuery
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Present primary-variable query facts; the name itself comes from the pinned image. -/
structure ParameterPresentQueryInput (sp env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (byte : Nat → BitVec 8) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 112
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  envNonzero : env ≠ 0#64
  search : SearchEntry (nativeStack sp 32) env entry (parameterName false) (parameterChars false).length byte c
  regs : GHolds c.σ (parameterQueryRegs false sp s0 s1 s2 s3 s4 s5 s6)

/-- The primary parser JAL and full successful secure getenv return. -/
theorem parameter_present_query (c : Config) (sp env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (byte : Nat → BitVec 8) (h : ParameterPresentQueryInput sp env entry ra s0 s1 s2 s3 s4 s5 s6 byte c) :
    FnSummary (parameterCall false).pc (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (securePresentLog sp (parameterCall false).link s0 s1 s2 s3 s4 s5 s6 (nameCursor entry (parameterChars false).length))
        c (parameterCall false).link (nameCursor entry (parameterChars false).length + 1#64)
        (getenvPresentRegs sp (parameterCall false).link s0 s1 s2 s3 s4 s5 s6 env entry (parameterName false) (parameterChars false).length)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have call := call_registers_summary (parameterCall_shape false) (parameterCall_decode false) c
    (parameterCall_pins false h.image) h.good h.image h.tick h.minstret _ h.regs
    (by simp only [parameterQueryRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [KeysAvoidRa, parameterQueryRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide) (by rfl)
  obtain ⟨mid, run1, called⟩ := call.run c ⟨pc, rfl⟩
  have input : GetenvPresentInput sp env entry (parameterName false) (parameterCall false).link s0 s1 s2 s3 s4 s5 s6
      (parameterChars false) byte mid := {
    toLeafInput := called.leaf (by rfl) (by decide)
    frame := h.frame
    regs := holds_project called.regs (by simp [getenvPrefixInput, parameterQueryRegs, getenvSavedRegs, lookupG])
    saved := holds_project called.regs (by simp [getenvSavedRegs, parameterQueryRegs, lookupG])
    saved0 := gholds_lookup (n := 8) _ called.regs (by rfl)
    query := parameter_name false called.image
    nameBelow := parameter_name_below false h.frame
    environment := by rw [called.memory]; exact h.environment
    envNonzero := h.envNonzero
    search := h.search.same_mem called.memory }
  obtain ⟨after, run2, post⟩ := (secure_getenv_present mid sp env entry (parameterName false) _ s0 s1 s2 s3 s4 s5 s6 (parameterChars false) byte input).run mid ⟨called.pc, rfl⟩
  have effects := (called.toEffectPost.trans post.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨after, run1.trans run2, ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, ?_, effects.output, effects.frame⟩, post.regs⟩⟩
  have same : mid.σ.mem = c.σ.mem := called.memory
  rw [post.memory, same]
end OCaml.Vm.Boot.Startup
