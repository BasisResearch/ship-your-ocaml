import OCaml.Vm.Boot.Startup.FindPrelude
import OCaml.Vm.Boot.Startup.FindLoaded
import OCaml.Vm.Boot.Startup.FindCompare
import OCaml.Vm.Boot.Startup.FindCount
import OCaml.Vm.Boot.Startup.FindSearchMemory
import OCaml.Vm.Boot.Startup.FindSkip
import OCaml.Vm.Boot.Startup.FindTail
import OCaml.Vm.Boot.Startup.StrncmpDiffer
import OCaml.Vm.Boot.Startup.Environment
import OCaml.Vm.Primitives.LibraryEffects
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A one-entry environment whose entry differs from the query name in its
first byte. All observed bytes lie below `_findenv_r`'s native frame. -/
structure FindMissInput (sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (l r : BitVec 8) (c : Config) : Prop
    extends FindPreludeInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c where
  saved0 : gprGet c.σ 8 = some s0
  array : ReadWindow env 8
  first : bytesT c.σ.mem env.toNat 8 = entry
  entryNonnull : entry ≠ 0#64
  next : ReadWindow (env + 8#64) 8
  last : bytesT c.σ.mem (env + 8#64).toNat 8 = 0#64
  arrayBelow : (env + 8#64).toNat + 8 ≤ nativeFrameBase sp 80
  firstBelow : env.toNat + 8 ≤ nativeFrameBase sp 80
  entryWindow : ReadWindow entry 1
  nameWindow : ReadWindow name 1
  entryByte : (c.σ.mem[entry.toNat]?).getD 0 = l
  nameByte : (c.σ.mem[name.toNat]?).getD 0 = r
  differ : l ≠ r
  entryBelow : entry.toNat < nativeFrameBase sp 80
  unaligned : strncmpAlignment entry name ≠ 0#64
  small : cs.length < 2^31

def findMissRegs (sp ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64) : GRegs :=
  findReturnRegs sp ra s1 s2 s3 s5 s6 ++ [(20, s4), (8, s0)]

/-- The argument registers the failed comparison leaves behind. -/
def findMissScratch (entry name : BitVec 64) (count : Nat) (l r : BitVec 8) : GRegs :=
  [(11, name), (12, strncmpEnd entry (BitVec.ofNat 64 count)), (14, nameByteWord r), (15, nameByteWord l)]

/-- Complete `_findenv_r` over a one-entry environment that does not match:
the bounded comparison fails at the first byte, the null next entry ends the
search, and the lock is released before returning null. -/
theorem findenv_miss (c : Config) (sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (l r : BitVec 8)
    (h : FindMissInput sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 cs l r c) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6) c ra 0#64
        (findMissRegs sp ra s0 s1 s2 s3 s4 s5 s6 ++ findMissScratch entry name cs.length l r)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, prepared⟩ := (find_prelude c sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs
    h.toFindPreludeInput).run c ⟨pc, rfl⟩
  have firstA : bytesT a.σ.mem env.toNat 8 = entry := by
    rw [prepared.memory, native_log_read_below c.σ.mem (findLog_inside h.frame) h.firstBelow]
    exact h.first
  obtain ⟨b, run2, loaded⟩ := (find_loaded a env entry _ (prepared.leaf (by rfl) (by decide))
    ⟨gholds_lookup (n := 9) _ prepared.regs (by rfl), gholds_lookup (n := 14) _ prepared.regs (by rfl), trivial⟩
    h.array firstA h.entryNonnull).run a ⟨prepared.pc, rfl⟩
  have keptA (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31) (unwritten : n ∉ [20, 10])
      (hv : gprGet a.σ n = some v) : gprGet b.σ n = some v :=
    (loaded.toEffectPost.gpr_frame (by decide) n lower upper unwritten).trans hv
  have regsB : GHolds b.σ (findCompareInput sp s0 name (nameCursor name cs.length) entry) :=
    ⟨keptA 2 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 2) _ prepared.regs (by rfl)),
      keptA 8 _ (by decide) (by decide) (by decide)
        ((prepared.toEffectPost.gpr_frame (by decide) 8 (by decide) (by decide) (by decide)).trans h.saved0),
      keptA 12 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ prepared.regs (by rfl)),
      keptA 18 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 18) _ prepared.regs (by rfl)),
      loaded.result, trivial⟩
  have leafB : LeafInput jal_80037468_call.link b := ⟨loaded.good, loaded.image, loaded.minstret,
    (loaded.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ prepared.regs (by rfl)),
    by decide, loaded.tick⟩
  obtain ⟨d, run3, compared⟩ := (find_compare b sp s0 name _ entry _ leafB h.frame regsB).run b ⟨loaded.pc, rfl⟩
  have countEq := findCompareCount_cursor name cs.length h.small
  have args : GHolds d.σ [(10, entry), (11, name), (12, BitVec.ofNat 64 cs.length)] := by
    have hs := compared.regs
    change GHolds d.σ (findCompareRegs sp name (nameCursor name cs.length) entry) at hs
    unfold findCompareRegs at hs
    rw [countEq] at hs
    exact ⟨gholds_lookup (n := 10) _ hs (by rfl), gholds_lookup (n := 11) _ hs (by rfl),
      gholds_lookup (n := 12) _ hs (by rfl), trivial⟩
  obtain ⟨e, run4, called⟩ := (call_registers_summary jal_800374c8_call_shape jal_800374c8_call_decode d
    (jal_800374c8_call_pins compared.image) compared.good compared.image compared.tick compared.minstret
    _ args (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) (by rfl)).run d
    ⟨compared.pc, rfl⟩
  have memoryE : e.σ.mem = writeLog c.σ.mem (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
    have same : b.σ.mem = a.σ.mem := loaded.memory
    rw [called.memory, compared.memory, same, prepared.memory, findSearchLog_eq, writeLog_append]
  have byteE (p : Nat) (below : p < nativeFrameBase sp 80) : (e.σ.mem[p]?).getD 0 = (c.σ.mem[p]?).getD 0 := by
    rw [memoryE, frameOn_writeLog _ _ _ (findSearchLog_inside h.frame) p ⟨Or.inl below, trivial⟩]
  have positive : BitVec.ofNat 64 cs.length ≠ 0#64 := by
    intro zero
    have := congrArg BitVec.toNat zero
    have bound : cs.length < 2^64 := by have := h.small; omega
    rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt bound] at this
    have := h.positive
    omega
  have nameBelow : name.toNat < nativeFrameBase sp 80 := by have := h.nameBelow; omega
  obtain ⟨f, run5, differed⟩ := (strncmp_mismatch e entry name _ _ l r (called.leaf (by rfl) (by decide))
    ⟨gholds_lookup (n := 10) _ called.regs (by rfl), gholds_lookup (n := 11) _ called.regs (by rfl),
      gholds_lookup (n := 12) _ called.regs (by rfl), gholds_lookup (n := 1) _ called.regs (by rfl), trivial⟩
    positive h.unaligned h.entryWindow h.nameWindow
    ((byteE _ h.entryBelow).trans h.entryByte) ((byteE _ nameBelow).trans h.nameByte) h.differ).run e
    ⟨called.pc, rfl⟩
  have sameF : f.σ.mem = e.σ.mem := differed.memory
  have keptD (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [8, 12, 11] ∧ n ∉ [1] ∧ n ∉ [15, 10, 14, 12])
      (hv : gprGet b.σ n = some v) : gprGet f.σ n = some v :=
    (differed.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.2).trans
      ((called.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2.1).trans
        ((compared.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans hv))
  have regsF : GHolds f.σ (findSkipInput sp env reent (strncmpDiff l r)) :=
    ⟨differed.result,
      keptD 9 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 9) _ loaded.regs (by rfl)),
      keptD 2 _ (by decide) (by decide) (by decide) (regsB.1),
      keptD 21 _ (by decide) (by decide) (by decide)
        (keptA 21 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ prepared.regs (by rfl))),
      trivial⟩
  have memoryF : f.σ.mem = writeLog c.σ.mem (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6) := sameF.trans memoryE
  obtain ⟨saved, saved4, saved0⟩ := findSearch_saved h.frame memoryF
  have lastF : bytesT f.σ.mem (env + 8#64).toNat 8 = 0#64 := by
    rw [memoryF, native_log_read_below c.σ.mem (findSearchLog_inside h.frame) h.arrayBelow]
    exact h.last
  obtain ⟨g, run6, skipped⟩ := (find_skip f sp env reent _ s0 s4 _ (differed.leaf (by rfl) (by decide)) h.frame
    regsF (strncmpDiff_ne h.differ) h.next lastF saved0 saved4).run f ⟨differed.pc, rfl⟩
  have sameG : g.σ.mem = f.σ.mem := skipped.memory
  have leafG : LeafInput jal_800374c8_call.link g := ⟨skipped.good, skipped.image, skipped.minstret,
    (skipped.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ differed.regs (by rfl)),
    by decide, skipped.tick⟩
  obtain ⟨after, run7, released⟩ := (find_release g sp reent ra s1 s2 s3 s5 s6 _ leafG h.frame
    ⟨gholds_lookup (n := 21) _ skipped.regs (by rfl), gholds_lookup (n := 2) _ skipped.regs (by rfl), trivial⟩
    (saved.transport sameG) h.aligned).run g ⟨skipped.pc, rfl⟩
  have effects := ((((((prepared.toEffectPost.trans loaded.toEffectPost).trans compared.toEffectPost).trans
    called.toEffectPost).trans differed.toEffectPost).trans skipped.toEffectPost).trans released.toEffectPost).widen
      (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨after, run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))),
    ⟨{ effects with memory := released.memory.trans (sameG.trans memoryF) }, ?_⟩⟩
  have scratch (n : Nat) (v : BitVec 64) (lower : 1 ≤ n) (upper : n ≤ 31)
      (unwritten : n ∉ [20, 8, 9, 10] ∧ n ∉ [10, 1, 9, 18, 19, 21, 22, 2])
      (hv : gprGet f.σ n = some v) : gprGet after.σ n = some v :=
    (released.toEffectPost.gpr_frame (by decide) n lower upper unwritten.2).trans
      ((skipped.toEffectPost.gpr_frame (by decide) n lower upper unwritten.1).trans hv)
  apply (gholds_append _ _).mpr
  refine ⟨(gholds_append _ _).mpr ⟨released.regs, ?_, ?_, trivial⟩, ?_⟩
  · exact (released.frame .x20 (by decide) (by decide)).trans (gholds_lookup (n := 20) _ skipped.regs (by rfl))
  · exact (released.frame .x8 (by decide) (by decide)).trans (gholds_lookup (n := 8) _ skipped.regs (by rfl))
  · exact ⟨scratch 11 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 11) _ differed.regs (by rfl)),
      scratch 12 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 12) _ differed.regs (by rfl)),
      scratch 14 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 14) _ differed.regs (by rfl)),
      scratch 15 _ (by decide) (by decide) (by decide) (gholds_lookup (n := 15) _ differed.regs (by rfl)),
      trivial⟩
end OCaml.Vm.Boot.Startup
