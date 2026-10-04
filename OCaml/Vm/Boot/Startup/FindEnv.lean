import OCaml.Vm.Boot.Startup.FindSaved
import OCaml.Vm.Boot.Startup.NameEmpty
import OCaml.Vm.Boot.Startup.FindTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findEnvRegs (sp ra s1 s2 s3 s4 s5 s6 name : BitVec 64) (count : Nat) : GRegs :=
  (findReturnRegs sp ra s1 s2 s3 s5 s6 ++ [(20, s4)]) ++
    [(12, nameCursor name count), (14, 0#64), (15, -61#64)]

/-- Reusable empty-environment input: a nonempty ordinary name, caller frame,
and the two environment observations supplied by startup memory. -/
structure FindEnvInput (sp reent name offset env ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (c : Config) : Prop extends LeafInput ra c where
  regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)
  saved4 : gprGet c.σ 20 = some s4
  frame : NativeFrame sp 80
  data : EnvName name cs c
  positive : 0 < cs.length
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 80
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  nonnull : env ≠ 0#64
  envWindow : ReadWindow env 8
  empty : bytesT c.σ.mem env.toNat 8 = 0#64
  envBelow : env.toNat + 8 ≤ nativeFrameBase sp 80

/-- Complete `_findenv_r` for an empty environment: save, lock, scan, inspect
the null first entry, unlock, restore and return null. -/
theorem findenv_empty (c : Config) (sp reent name offset env ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (h : FindEnvInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 9, 10, 12, 14, 15, 18, 19, 20, 21, 22]
        (findLog sp ra s1 s2 s3 s4 s5 s6) c ra 0#64
        (findEnvRegs sp ra s1 s2 s3 s4 s5 s6 name cs.length)) := by
  constructor
  intro before input
  obtain ⟨pc, eq⟩ := input
  subst before
  obtain ⟨a, run1, locked⟩ := (find_locked c sp reent name offset ra s1 s2 s3 s5 s6 h.toLeafInput h.frame h.regs).run c ⟨pc, rfl⟩
  have dataA := h.data.stack_log h.nameBelow (findPrefix_log_inside h.frame) locked.memory
  have envA : bytesT a.σ.mem Layout.sym_environ 8 = env := by
    rw [locked.memory, native_log_read_below c.σ.mem (findPrefix_log_inside h.frame) ?_]
    · exact h.environment
    · have low := h.frame.lower
      have envBound : Layout.sym_environ + 8 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
      unfold nativeFrameBase
      omega
  have regsA : GHolds a.σ (findStartInput sp name s4 (envLockValue false)) :=
    ⟨gholds_lookup (n := 19) _ locked.regs (by rfl), gholds_lookup (n := 2) _ locked.regs (by rfl),
      (locked.frame .x20 (by decide) (by decide)).trans h.saved4,
      gholds_lookup (n := 18) _ locked.regs (by rfl), locked.result, trivial⟩
  obtain ⟨byte, startInput⟩ := findStart_of_name (locked.leaf (by rfl) (by decide)) h.frame regsA dataA
    h.positive h.nameBelow envA h.nonnull
  obtain ⟨b, run2, started⟩ := (find_start a sp name s4 (envLockValue false) env _ byte startInput).run a ⟨locked.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (findLog sp ra s1 s2 s3 s4 s5 s6) := by
    rw [started.memory, locked.memory, findLog_eq, writeLog_append]
  have dataB := h.data.stack_log h.nameBelow (findLog_inside h.frame) memoryB
  have emptyB : bytesT b.σ.mem env.toNat 8 = 0#64 := by
    rw [memoryB, native_log_read_below c.σ.mem (findLog_inside h.frame) h.envBelow]
    exact h.empty
  have leafB : LeafInput jal_80037468_call.link b :=
    ⟨started.good, started.image, started.minstret,
      (started.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ locked.regs (by rfl)),
      by decide, started.tick⟩
  obtain ⟨d, run3, scanned⟩ := (name_scan_empty b name env _ (envLockValue false) cs dataB h.positive leafB
    (gholds_lookup (n := 12) _ started.regs (by rfl)) started.result
    (gholds_lookup (n := 9) _ started.regs (by rfl)) h.envWindow emptyB).run b ⟨started.pc, rfl⟩
  have memoryD : d.σ.mem = writeLog c.σ.mem (findLog sp ra s1 s2 s3 s4 s5 s6) := scanned.memory.trans memoryB
  obtain ⟨saved, saved4⟩ := find_saved h.frame memoryD
  have leafD : LeafInput jal_80037468_call.link d :=
    ⟨scanned.good, scanned.image, scanned.minstret,
      (scanned.frame .x1 (by decide) (by decide)).trans leafB.raReg, by decide, scanned.tick⟩
  have regsD : GHolds d.σ (findRestoreInput sp reent) := ⟨
    (scanned.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ started.regs (by rfl)),
    (scanned.frame .x21 (by decide) (by decide)).trans ((started.frame .x21 (by decide) (by decide)).trans
      (gholds_lookup (n := 21) _ locked.regs (by rfl))), scanned.result, trivial⟩
  obtain ⟨after, run4, post⟩ := (find_tail d sp reent ra s1 s2 s3 s4 s5 s6 _ leafD h.frame regsD saved4 saved h.aligned).run d ⟨scanned.pc, rfl⟩
  have effects := ((locked.toEffectPost.trans started.toEffectPost).trans scanned.toEffectPost).trans post.toEffectPost
  refine ⟨after, run1.trans (run2.trans (run3.trans run4)), ⟨?_, ?_⟩⟩
  · exact { effects.widen (writes' := [1, 2, 9, 10, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide) with
      memory := post.memory.trans memoryD }
  · apply (gholds_append _ _).mpr
    exact ⟨post.regs,
      (post.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ scanned.regs (by rfl)),
      (post.frame .x14 (by decide) (by decide)).trans (gholds_lookup (n := 14) _ scanned.regs (by rfl)),
      (post.frame .x15 (by decide) (by decide)).trans (gholds_lookup (n := 15) _ scanned.regs (by rfl)), trivial⟩
end OCaml.Vm.Boot.Startup
