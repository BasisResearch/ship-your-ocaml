import OCaml.Vm.Boot.Startup.GetenvPresentMemory
import OCaml.Vm.Boot.Startup.GetenvReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

structure GetenvPresentInput (sp env entry name ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (byte : Nat → BitVec 8) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 112
  regs : GHolds c.σ (getenvPrefixInput sp name ra)
  saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)
  saved0 : gprGet c.σ 8 = some s0
  query : EnvName name cs c
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 112
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  envNonzero : env ≠ 0#64
  search : SearchEntry (nativeStack sp 32) env entry name cs.length byte c

def getenvPresentKeptRegs (s0 s1 s2 s3 s4 s5 s6 env entry name : BitVec 64) (count : Nat) : GRegs :=
  [(8, s0)] ++ getenvSavedRegs s1 s2 s3 s4 s5 s6 ++
    [(11, nameCursor name count), (12, nameCursor entry (count - 1)), (14, env), (15, nameCursor entry count)]
def getenvPresentRegs (sp ra s0 s1 s2 s3 s4 s5 s6 env entry name : BitVec 64) (count : Nat) : GRegs :=
  getenvReturnRegs sp ra (nameCursor entry count + 1#64) ++
    getenvPresentKeptRegs s0 s1 s2 s3 s4 s5 s6 env entry name count

/-- Complete getenv for a matching first entry, including its nested caller
output slot and restored original stack/link. -/
theorem getenv_present (c : Config) (sp env entry name ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (byte : Nat → BitVec 8)
    (h : GetenvPresentInput sp env entry name ra s0 s1 s2 s3 s4 s5 s6 cs byte c) :
    FnSummary 0x80037410#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry cs.length))
        c ra (nameCursor entry cs.length + 1#64)
        (getenvPresentRegs sp ra s0 s1 s2 s3 s4 s5 s6 env entry name cs.length)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have outer := h.frame.resize (small := 32) (by decide) (by decide)
  have inner := h.frame.nested (front := 32) (size := 80) (by decide)
  have innerBase := h.frame.nested_base (front := 32) (size := 80) (by decide)
  obtain ⟨a, run1, called⟩ := (getenv_to_find c sp name ra s1 s2 s3 s4 s5 s6 h.toLeafInput outer h.regs h.saved).run c ⟨pc, rfl⟩
  have inside : LogInW [⟨nativeFrameBase sp 112, sp.toNat⟩] (getenvLog sp ra) := by
    apply log_in_larger_window (getenvLog_inside outer)
    · change nativeFrameBase sp 112 ≤ nativeFrameBase sp 32
      unfold nativeFrameBase
      omega
    · exact Nat.le_refl _
  have searchA := h.search.stack_log (by rw [innerBase]; exact inside) called.memory
  have queryA := h.query.stack_log h.nameBelow inside called.memory
  have envA : bytesT a.σ.mem Layout.sym_environ 8 = env := by
    rw [called.memory, native_log_read_below c.σ.mem inside ?_]
    · exact h.environment
    · have lower := h.frame.lower
      have global : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
      unfold nativeFrameBase
      omega
  have input : FindPresentInput (nativeStack sp 32) (getenvReent c) name (nativeStack sp 32 + 12#64)
      env entry jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6 cs byte a := {
    toLeafInput := called.leaf (by rfl) (by decide)
    frame := inner
    regs := holds_project called.regs (by simp [findPrefixInput, getenvCallRegs, getenvSavedRegs, lookupG])
    saved4 := gholds_lookup (n := 20) _ called.regs (by rfl)
    data := queryA
    positive := h.search.positive
    nameBelow := by rw [innerBase]; exact h.nameBelow
    environment := envA
    nonnull := h.envNonzero
    search := searchA
    saved0 := (called.frame .x8 (by decide) (by decide)).trans h.saved0
    slot := getenv_offset_window outer
    offsetHigh := by
      rw [nativeStack, outer.address 12 (by decide), outer.slot_nat (by decide)]
      rw [← nativeStack, outer.stack_nat]
      omega
    storesOutside := h.frame.image_outside (getenv_found_inside h.frame) }
  obtain ⟨b, run2, found⟩ := (findenv_present a _ _ _ _ env entry _ s0 s1 s2 s3 s4 s5 s6 cs byte input).run a ⟨called.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry cs.length)) := by
    rw [found.memory, called.memory, getenvPresentLog, writeLog_append]
  have savedRa := getenv_present_saved h.frame memoryB
  have regsB : GHolds b.σ (getenvReturnInput sp (nameCursor entry cs.length + 1#64)) :=
    ⟨gholds_lookup (n := 2) _ found.regs (by rfl), found.result, trivial⟩
  obtain ⟨after, run3, returned⟩ := (getenv_return b sp ra _ (found.leaf (by rfl) (by decide)) outer regsB savedRa h.aligned).run b ⟨found.pc, rfl⟩
  have parked : GHolds b.σ (getenvPresentKeptRegs s0 s1 s2 s3 s4 s5 s6 env entry name cs.length) :=
    holds_project found.regs (by simp [getenvPresentKeptRegs, getenvSavedRegs, findPresentRegs, findFoundReturnRegs, lookupG])
  have kept := holds_frame_ne returned.frame parked
    (by simp only [getenvPresentKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvPresentKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvPresentKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
  have effects := ((called.toEffectPost.trans found.toEffectPost).trans returned.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  exact ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, returned.memory.trans memoryB, effects.output, effects.frame⟩,
    (gholds_append _ _).mpr ⟨returned.regs, kept⟩⟩⟩
end OCaml.Vm.Boot.Startup
