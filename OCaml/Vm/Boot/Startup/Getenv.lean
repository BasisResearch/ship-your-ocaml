import OCaml.Vm.Boot.Startup.GetenvMemory
import OCaml.Vm.Boot.Startup.GetenvReturn
import OCaml.Vm.Boot.Startup.FindEnv
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def getenvKeptRegs (s1 s2 s3 s4 s5 s6 name : BitVec 64) (count : Nat) : GRegs :=
  getenvSavedRegs s1 s2 s3 s4 s5 s6 ++ [(11, name), (12, nameCursor name count), (14, 0#64), (15, -61#64)]
def getenvRegs (sp ra s1 s2 s3 s4 s5 s6 name : BitVec 64) (count : Nat) : GRegs :=
  getenvReturnRegs sp ra ++ getenvKeptRegs s1 s2 s3 s4 s5 s6 name count

structure GetenvInput (sp name env ra s1 s2 s3 s4 s5 s6 : BitVec 64) (cs : List Char) (c : Config) : Prop extends LeafInput ra c, EmptyEnvironment sp 112 env c where
  regs : GHolds c.σ (getenvPrefixInput sp name ra)
  saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)
  data : EnvName name cs c
  positive : 0 < cs.length
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 112

/-- Complete getenv for an empty embedded environment, including both nested
caller frames and the generated reentrancy-pointer load. -/
theorem getenv_empty (c : Config) (sp name env ra s1 s2 s3 s4 s5 s6 : BitVec 64) (cs : List Char)
    (h : GetenvInput sp name env ra s1 s2 s3 s4 s5 s6 cs c) :
    FnSummary 0x80037410#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (getenvFullLog sp ra s1 s2 s3 s4 s5 s6) c ra 0#64
        (getenvRegs sp ra s1 s2 s3 s4 s5 s6 name cs.length)) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  have outer := h.frame.resize (small := 32) (by decide) (by decide)
  have inner := h.frame.nested (front := 32) (size := 80) (by decide)
  have innerBase := h.frame.nested_base (front := 32) (size := 80) (by decide)
  have baseOrder : nativeFrameBase sp 112 ≤ nativeFrameBase sp 32 := by unfold nativeFrameBase; omega
  obtain ⟨a, run1, called⟩ := (getenv_to_find c sp name ra s1 s2 s3 s4 s5 s6 h.toLeafInput outer h.regs h.saved).run c ⟨pc, rfl⟩
  have envA := h.toEmptyEnvironment.stack_log
    (log_in_larger_window (getenvLog_inside outer) baseOrder (Nat.le_refl _)) called.memory
  have searchInput : FindEnvInput (nativeStack sp 32) (getenvReent c) name (nativeStack sp 32 + 12#64)
      env jal_80037428_call.link s1 s2 s3 s4 s5 s6 cs a := {
    toLeafInput := called.leaf (by rfl) (by decide)
    regs := holds_project called.regs (by simp [getenvCallRegs, getenvSavedRegs, findPrefixInput, lookupG])
    saved4 := gholds_lookup (n := 20) _ called.regs (by rfl)
    toEmptyEnvironment := envA.reframe inner (by rw [innerBase]; exact Nat.le_refl _)
    data := h.data.stack_log (Nat.le_trans h.nameBelow baseOrder) (getenvLog_inside outer) called.memory
    positive := h.positive
    nameBelow := by rw [innerBase]; exact h.nameBelow }
  obtain ⟨b, run2, found⟩ := (findenv_empty a _ _ _ _ _ _ _ _ _ _ _ _ cs searchInput).run a ⟨called.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (getenvFullLog sp ra s1 s2 s3 s4 s5 s6) := by
    rw [found.memory, called.memory, getenvFullLog, writeLog_append]
  have regsB : GHolds b.σ (getenvReturnInput sp) :=
    ⟨gholds_lookup (n := 2) _ found.regs (by rfl), found.result, trivial⟩
  obtain ⟨after, run3, post⟩ := (getenv_return b sp ra _ (found.leaf (by rfl) (by decide)) outer regsB
    (getenv_saved h.frame memoryB) h.aligned).run b ⟨found.pc, rfl⟩
  have keptB : GHolds b.σ (getenvKeptRegs s1 s2 s3 s4 s5 s6 name cs.length) := by
    apply (gholds_append _ _).mpr
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · exact holds_project found.regs (by simp [getenvSavedRegs, findEnvRegs, findReturnRegs, lookupG])
    · exact (found.frame .x11 (by decide) (by decide)).trans (gholds_lookup (n := 11) _ called.regs (by rfl))
    · exact gholds_lookup (n := 12) _ found.regs (by rfl)
    · exact gholds_lookup (n := 14) _ found.regs (by rfl)
    · exact gholds_lookup (n := 15) _ found.regs (by rfl)
  have kept := holds_frame_ne post.frame keptB
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
  have effects := (called.toEffectPost.trans found.toEffectPost).trans post.toEffectPost
  refine ⟨after, run1.trans (run2.trans run3), ⟨?_, (gholds_append _ _).mpr ⟨post.regs, kept⟩⟩⟩
  exact { effects.widen (writes' := [1, 2, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide) with
    memory := post.memory.trans memoryB }
end OCaml.Vm.Boot.Startup
