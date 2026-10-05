import OCaml.Vm.Boot.Startup.GetenvPresentMemory
import OCaml.Vm.Boot.Startup.GetenvReturn
import OCaml.Vm.Boot.Startup.FindMiss
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- getenv's saved link survives any nested-call log kept below its slot. -/
theorem getenv_saved_below {sp ra inner} {before after : Config} (frame : NativeFrame sp 112)
    (below : LogInW [⟨nativeFrameBase sp 112, nativeFrameBase sp 32 + 16⟩] inner)
    (memory : after.σ.mem = writeLog before.σ.mem (getenvLog sp ra ++ inner)) :
    bytesT after.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra := by
  rw [memory, writeLog_append,
    bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows below ?_)]
  · exact (frame.resize (small := 32) (by decide) (by decide)).word_log_read
      (slots := [(24, ra)]) (by intro off value member; cases List.mem_singleton.mp member; decide)
      (by simp) before.σ.mem (by simp)
  · exact ⟨Or.inr (by dsimp only; omega), trivial⟩

theorem getenv_miss_below_caller {sp ra s0 s1 s2 s3 s4 s5 s6} (frame : NativeFrame sp 112) :
    LogInW [⟨nativeFrameBase sp 112, nativeFrameBase sp 32 + 16⟩]
      (findSearchLog (nativeStack sp 32) ra s0 s1 s2 s3 s4 s5 s6) := by
  have inner := frame.nested (front := 32) (size := 80) (by decide)
  apply log_in_larger_window (findSearchLog_inside inner)
  · change nativeFrameBase sp 112 ≤ nativeFrameBase (nativeStack sp 32) 80
    rw [frame.nested_base (front := 32) (size := 80) (by decide)]
    exact Nat.le_refl _
  · change (nativeStack sp 32).toNat ≤ nativeFrameBase sp 32 + 16
    rw [(frame.resize (small := 32) (by decide) (by decide)).stack_nat]
    omega

def getenvMissLog (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : List WEntry :=
  getenvLog sp ra ++ findSearchLog (nativeStack sp 32) jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6

/-- A one-entry environment whose entry differs from the query in its first
byte, observed from getenv's caller. -/
structure GetenvMissInput (sp env entry name ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (l r : BitVec 8) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 112
  regs : GHolds c.σ (getenvPrefixInput sp name ra)
  saved : GHolds c.σ (getenvSavedRegs s1 s2 s3 s4 s5 s6)
  saved0 : gprGet c.σ 8 = some s0
  query : EnvName name cs c
  positive : 0 < cs.length
  small : cs.length < 2^31
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 112
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  envNonzero : env ≠ 0#64
  array : ReadWindow env 8
  first : bytesT c.σ.mem env.toNat 8 = entry
  entryNonnull : entry ≠ 0#64
  next : ReadWindow (env + 8#64) 8
  last : bytesT c.σ.mem (env + 8#64).toNat 8 = 0#64
  arrayBelow : (env + 8#64).toNat + 8 ≤ nativeFrameBase sp 112
  firstBelow : env.toNat + 8 ≤ nativeFrameBase sp 112
  entryWindow : ReadWindow entry 1
  nameWindow : ReadWindow name 1
  entryByte : (c.σ.mem[entry.toNat]?).getD 0 = l
  nameByte : (c.σ.mem[name.toNat]?).getD 0 = r
  differ : l ≠ r
  entryBelow : entry.toNat < nativeFrameBase sp 112
  unaligned : strncmpAlignment entry name ≠ 0#64

def getenvMissKeptRegs (s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  [(8, s0)] ++ getenvSavedRegs s1 s2 s3 s4 s5 s6

/-- Complete getenv for a name absent from a one-entry environment: null. -/
theorem getenv_miss (c : Config) (sp env entry name ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (l r : BitVec 8) (h : GetenvMissInput sp env entry name ra s0 s1 s2 s3 s4 s5 s6 cs l r c) :
    FnSummary 0x80037410#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (getenvMissLog sp ra s0 s1 s2 s3 s4 s5 s6) c ra 0#64
        (getenvReturnRegs sp ra ++ getenvMissKeptRegs s0 s1 s2 s3 s4 s5 s6)) := by
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
  have wordA (p : Nat) (below : p + 8 ≤ nativeFrameBase sp 112) : bytesT a.σ.mem p 8 = bytesT c.σ.mem p 8 := by
    rw [called.memory, native_log_read_below c.σ.mem inside below]
  have byteA (p : Nat) (below : p < nativeFrameBase sp 112) : (a.σ.mem[p]?).getD 0 = (c.σ.mem[p]?).getD 0 := by
    rw [called.memory, frameOn_writeLog _ _ _ inside p ⟨Or.inl below, trivial⟩]
  have envA : bytesT a.σ.mem Layout.sym_environ 8 = env := by
    rw [wordA _ ?_]
    · exact h.environment
    · have lower := h.frame.lower
      have global : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
      unfold nativeFrameBase
      omega
  have nameBelow : name.toNat < nativeFrameBase sp 112 := by have := h.nameBelow; omega
  have input : FindMissInput (nativeStack sp 32) (getenvReent c) name (nativeStack sp 32 + 12#64)
      env entry jal_80037428_call.link s0 s1 s2 s3 s4 s5 s6 cs l r a := {
    toLeafInput := called.leaf (by rfl) (by decide)
    frame := inner
    regs := holds_project called.regs (by simp [findPrefixInput, getenvCallRegs, getenvSavedRegs, lookupG])
    saved4 := gholds_lookup (n := 20) _ called.regs (by rfl)
    data := h.query.stack_log h.nameBelow inside called.memory
    positive := h.positive
    nameBelow := by rw [innerBase]; exact h.nameBelow
    environment := envA
    nonnull := h.envNonzero
    saved0 := (called.frame .x8 (by decide) (by decide)).trans h.saved0
    array := h.array
    first := (wordA _ h.firstBelow).trans h.first
    entryNonnull := h.entryNonnull
    next := h.next
    last := (wordA _ h.arrayBelow).trans h.last
    arrayBelow := by rw [innerBase]; exact h.arrayBelow
    firstBelow := by rw [innerBase]; exact h.firstBelow
    entryWindow := h.entryWindow
    nameWindow := h.nameWindow
    entryByte := (byteA _ h.entryBelow).trans h.entryByte
    nameByte := (byteA _ nameBelow).trans h.nameByte
    differ := h.differ
    entryBelow := by rw [innerBase]; exact h.entryBelow
    unaligned := h.unaligned
    small := h.small }
  obtain ⟨b, run2, missed⟩ := (findenv_miss a _ _ _ _ env entry _ s0 s1 s2 s3 s4 s5 s6 cs l r input).run a ⟨called.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (getenvMissLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
    rw [missed.memory, called.memory, getenvMissLog, writeLog_append]
  have savedRa := getenv_saved_below h.frame (getenv_miss_below_caller h.frame) memoryB
  have regsB : GHolds b.σ (getenvReturnInput sp) :=
    ⟨gholds_lookup (n := 2) _ missed.regs (by rfl), missed.result, trivial⟩
  obtain ⟨after, run3, returned⟩ := (getenv_return b sp ra _ (missed.leaf (by rfl) (by decide)) outer regsB
    savedRa h.aligned).run b ⟨missed.pc, rfl⟩
  have parked : GHolds b.σ (getenvMissKeptRegs s0 s1 s2 s3 s4 s5 s6) :=
    holds_project missed.regs (by simp [getenvMissKeptRegs, getenvSavedRegs, findMissRegs, findReturnRegs, lookupG])
  have kept := holds_frame_ne returned.frame parked
    (by simp only [getenvMissKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvMissKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
    (by simp only [getenvMissKeptRegs, getenvSavedRegs, List.cons_append, List.nil_append, keysG]; decide)
  have effects := ((called.toEffectPost.trans missed.toEffectPost).trans returned.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  exact ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, returned.memory.trans memoryB, effects.output, effects.frame⟩,
    (gholds_append _ _).mpr ⟨returned.regs, kept⟩⟩⟩
end OCaml.Vm.Boot.Startup
