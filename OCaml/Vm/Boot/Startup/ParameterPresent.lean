import OCaml.Vm.Boot.Startup.ParameterPresentMemory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def parameterValuePointer (entry : BitVec 64) : BitVec 64 := nameCursor entry (parameterChars false).length + 1#64

structure ParameterPresentInput (sp env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (byte : Nat → BitVec 8) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 176
  regs : GHolds c.σ (parameterPrefixInput sp ra s0)
  saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  envNonzero : env ≠ 0#64
  search : SearchEntry (nativeStack (nativeStack sp 64) 32) env entry (parameterName false) (parameterChars false).length byte c
  valueWindow : ReadWindow (parameterValuePointer entry) 1
  valueZero : (c.σ.mem[(parameterValuePointer entry).toNat]?).getD 0 = 0#8
  valueBelow : (parameterValuePointer entry).toNat + 1 ≤ nativeFrameBase sp 176

def parameterPresentKept (env entry s4 s5 s6 : BitVec 64) : GRegs :=
  [(20, s4), (21, s5), (22, s6), (11, nameCursor (parameterName false) (parameterChars false).length),
   (12, nameCursor entry ((parameterChars false).length - 1)), (14, env)]
def parameterPresentRegs (sp env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  (parameterValueReturnRegs sp ra s0 s1 s2 s3 (parameterValuePointer entry) ++ [(15, 0#64)]) ++
    parameterPresentKept env entry s4 s5 s6

/-- The complete native parameter parser for a present primary variable whose
value is empty. This is the path selected by the pinned while_min environment. -/
theorem parse_parameters_present_empty (c : Config) (sp env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (byte : Nat → BitVec 8) (h : ParameterPresentInput sp env entry ra s0 s1 s2 s3 s4 s5 s6 byte c) :
    FnSummary 0x8000451c#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (parameterPresentLog sp entry ra s0 s1 s2 s3 s4 s5 s6) c ra (parameterValuePointer entry)
        (parameterPresentRegs sp env entry ra s0 s1 s2 s3 s4 s5 s6)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have outer := h.frame.resize (small := 64) (by decide) (by decide)
  have inner := h.frame.nested (front := 64) (size := 112) (by decide)
  have prefixInside : LogInW [⟨nativeFrameBase sp 176, sp.toNat⟩] (parameterLog sp ra s0) := by
    apply log_in_larger_window (parameterLog_inside outer)
    · change nativeFrameBase sp 176 ≤ nativeFrameBase sp 64
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  obtain ⟨a, run1, prepared⟩ := (parameter_prefix c sp ra s0 h.toLeafInput outer h.regs).run c ⟨pc, rfl⟩
  have savedA := holds_frame_ne prepared.frame h.saved
    (by simp only [getenvSavedRegs, keysG]; decide) (by simp only [getenvSavedRegs, keysG]; decide)
    (by simp only [getenvSavedRegs, keysG]; decide)
  have input : ParameterPresentQueryInput (nativeStack sp 64) env entry ra s0 s1 s2 s3 s4 s5 s6 byte a := {
    toLeafInput := prepared.leaf (by rfl) h.aligned
    frame := inner
    environment := by
      rw [prepared.memory, native_log_read_below c.σ.mem prefixInside ?_]
      · exact h.environment
      · have lower := h.frame.lower
        have global : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
        unfold nativeFrameBase
        omega
    envNonzero := h.envNonzero
    search := h.search.stack_log (by
      rw [inner.nested_base (front := 32) (size := 80) (by decide), h.frame.nested_base (front := 64) (size := 112) (by decide)]
      exact prefixInside) prepared.memory
    regs := (gholds_append _ _).mpr ⟨⟨prepared.result, gholds_lookup (n := 2) _ prepared.regs (by rfl),
      gholds_lookup (n := 8) _ prepared.regs (by rfl), trivial⟩, savedA⟩ }
  obtain ⟨b, run2, queried⟩ := (parameter_present_query a _ env entry ra s0 s1 s2 s3 s4 s5 s6 byte input).run a ⟨prepared.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (parameterPresentPrefixLog sp entry ra s0 s1 s2 s3 s4 s5 s6) := by
    rw [queried.memory, prepared.memory, parameterPresentPrefixLog, parameterPresentQueryLog, writeLog_append]
  obtain ⟨savedRa, saved0⟩ := parameter_present_saved h.frame memoryB
  have valueLogInside : LogInW [⟨nativeFrameBase sp 176, sp.toNat⟩] (parameterValueLog sp s1 s2 s3) := by
    apply log_in_larger_window (parameterValueLog_inside outer)
    · change nativeFrameBase sp 176 ≤ nativeFrameBase sp 64
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  have zero : ((writeLog b.σ.mem (parameterValueLog sp s1 s2 s3))[(parameterValuePointer entry).toNat]?).getD 0 = 0#8 := by
    rw [frameOn_writeLog _ _ _ valueLogInside _ ⟨Or.inl (by dsimp only; have := h.valueBelow; omega), trivial⟩,
      memoryB, frameOn_writeLog _ _ _ (parameterPresentPrefixLog_inside h.frame) _
        ⟨Or.inl (by dsimp only; have := h.valueBelow; omega), trivial⟩]
    exact h.valueZero
  have nonnull : parameterValuePointer entry ≠ 0#64 := by
    intro eq
    have lower := h.valueWindow.lower
    rw [eq] at lower
    contradiction
  have regsB : GHolds b.σ (parameterValueInput sp s1 s2 s3 (parameterValuePointer entry)) :=
    ⟨gholds_lookup (n := 2) _ queried.regs (by rfl), gholds_lookup (n := 9) _ queried.regs (by rfl),
      gholds_lookup (n := 18) _ queried.regs (by rfl), gholds_lookup (n := 19) _ queried.regs (by rfl), queried.result, trivial⟩
  obtain ⟨after, run3, returned⟩ := (parameter_value_done b sp ra _ s0 s1 s2 s3 (parameterValuePointer entry)
    (queried.leaf (by rfl) (by decide)) outer regsB nonnull h.valueWindow zero savedRa saved0 h.aligned).run b ⟨queried.pc, rfl⟩
  have parked : GHolds b.σ (parameterPresentKept env entry s4 s5 s6) :=
    holds_project queried.regs (by simp [parameterPresentKept, getenvPresentRegs, getenvReturnRegs, getenvPresentKeptRegs, getenvSavedRegs, lookupG])
  have kept := holds_frame_ne returned.frame parked (by simp only [parameterPresentKept, keysG]; decide)
    (by simp only [parameterPresentKept, keysG]; decide) (by simp only [parameterPresentKept, keysG]; decide)
  have effects := ((prepared.toEffectPost.trans queried.toEffectPost).trans returned.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, ?_, effects.output, effects.frame⟩, (gholds_append _ _).mpr ⟨returned.regs, kept⟩⟩⟩
  rw [returned.memory, memoryB, parameterPresentLog, writeLog_append]
end OCaml.Vm.Boot.Startup
