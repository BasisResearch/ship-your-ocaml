import OCaml.Vm.Boot.Startup.ParameterMemory
import OCaml.Vm.Boot.Startup.ParameterBranch
import OCaml.Vm.Boot.Startup.ParameterReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def parameterRegs (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  parameterReturnRegs sp ra s0 ++ getenvKeptRegs s1 s2 s3 s4 s5 s6 (parameterName true) (parameterChars true).length

structure ParameterInput (sp env ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) (c : Config) : Prop
    extends LeafInput ra c, EmptyEnvironment sp 176 env c where
  regs : GHolds c.σ (parameterPrefixInput sp ra s0)
  saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)

/-- The complete native parameter parser returns with defaults unchanged when
both certified environment names are absent. All calls and branches are proved. -/
theorem parse_parameters_empty (c : Config) (sp env ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (h : ParameterInput sp env ra s0 s1 s2 s3 s4 s5 s6 c) :
    FnSummary 0x8000451c#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (parameterFullLog sp ra s0 s1 s2 s3 s4 s5 s6) c ra 0#64
        (parameterRegs sp ra s0 s1 s2 s3 s4 s5 s6)) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  have outer := h.frame.resize (small := 64) (by decide) (by decide)
  have inner := h.frame.nested (front := 64) (size := 112) (by decide)
  have innerBase := h.frame.nested_base (front := 64) (size := 112) (by decide)
  obtain ⟨a, run1, prepared⟩ := (parameter_prefix c sp ra s0 h.toLeafInput outer h.regs).run c ⟨pc, rfl⟩
  have envA := h.toEmptyEnvironment.stack_log (parameter_prefix_inside h.frame) prepared.memory
  have savedA := holds_frame_ne prepared.frame h.saved
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
  have input0 : ParameterQueryInput false (nativeStack sp 64) env ra s0 s1 s2 s3 s4 s5 s6 a := {
    toLeafInput := prepared.leaf (by rfl) h.aligned
    toEmptyEnvironment := envA.reframe inner (by rw [innerBase]; exact Nat.le_refl _)
    regs := (gholds_append _ _).mpr ⟨⟨prepared.result, gholds_lookup (n := 2) _ prepared.regs (by rfl),
      gholds_lookup (n := 8) _ prepared.regs (by rfl), trivial⟩, savedA⟩ }
  obtain ⟨b, run2, first⟩ := (parameter_query false a _ env ra s0 s1 s2 s3 s4 s5 s6 input0).run a ⟨prepared.pc, rfl⟩
  have envB := input0.toEmptyEnvironment.stack_log (secureEnvLog_inside inner) first.memory
  obtain ⟨d, run3, fallback⟩ := (parameter_fallback b _ (first.leaf (by rfl) (by decide)) first.result).run b ⟨first.pc, rfl⟩
  have savedB : GHolds b.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6) :=
    holds_project first.regs (by simp [getenvSavedRegs, secureEnvRegs, getenvRegs, getenvReturnRegs, getenvKeptRegs, lookupG])
  have savedD := holds_frame_ne fallback.frame savedB
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
  have leafD : LeafInput (parameterCall false).link d :=
    ⟨fallback.good, fallback.image, fallback.minstret,
      (fallback.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ first.regs (by rfl)),
      by decide, fallback.tick⟩
  have input1 : ParameterQueryInput true (nativeStack sp 64) env (parameterCall false).link s0 s1 s2 s3 s4 s5 s6 d := {
    toLeafInput := leafD
    toEmptyEnvironment := envB.same_mem fallback.memory
    regs := (gholds_append _ _).mpr ⟨⟨fallback.result,
      (fallback.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ first.regs (by rfl)),
      (fallback.frame .x8 (by decide) (by decide)).trans (gholds_lookup (n := 8) _ first.regs (by rfl)), trivial⟩, savedD⟩ }
  obtain ⟨e, run4, second⟩ := (parameter_query true d _ env _ s0 s1 s2 s3 s4 s5 s6 input1).run d ⟨fallback.pc, rfl⟩
  obtain ⟨f, run5, missing⟩ := (parameter_second_missing e _ (second.leaf (by rfl) (by decide)) second.result).run e ⟨second.pc, rfl⟩
  have fallbackMemory : d.σ.mem = b.σ.mem := fallback.memory
  have missingMemory : f.σ.mem = e.σ.mem := missing.memory
  have memoryF : f.σ.mem = writeLog c.σ.mem (parameterFullLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
    rw [missingMemory, second.memory, fallbackMemory, first.memory, prepared.memory,
      parameterFullLog, parameterQueryLog, parameterQueryLog, writeLog_append, writeLog_append]
  obtain ⟨savedRa, saved0⟩ := parameter_saved h.frame memoryF
  have leafF : LeafInput (parameterCall true).link f :=
    ⟨missing.good, missing.image, missing.minstret,
      (missing.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ second.regs (by rfl)),
      by decide, missing.tick⟩
  have regsF : GHolds f.σ (parameterReturnInput sp) :=
    ⟨(missing.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ second.regs (by rfl)), missing.result, trivial⟩
  obtain ⟨after, run6, post⟩ := (parameter_return f sp ra s0 _ leafF outer regsF savedRa saved0 h.aligned).run f ⟨missing.pc, rfl⟩
  have keptE : GHolds e.σ (getenvKeptRegs s1 s2 s3 s4 s5 s6 (parameterName true) (parameterChars true).length) :=
    holds_project second.regs (by simp [secureEnvRegs, getenvRegs, getenvReturnRegs, getenvKeptRegs, getenvSavedRegs, lookupG])
  have keptF := holds_frame_ne missing.frame keptE
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
  have kept := holds_frame_ne post.frame keptF
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
  have effects := ((((prepared.toEffectPost.trans first.toEffectPost).trans fallback.toEffectPost).trans second.toEffectPost).trans missing.toEffectPost).trans post.toEffectPost
  have widened := effects.widen (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  exact ⟨after, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))),
    ⟨⟨widened.good, widened.image, widened.minstret, widened.tick, widened.pc, widened.result,
      post.memory.trans memoryF, widened.output, widened.frame⟩, (gholds_append _ _).mpr ⟨post.regs, kept⟩⟩⟩
end OCaml.Vm.Boot.Startup
