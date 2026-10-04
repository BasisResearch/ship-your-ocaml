import OCaml.Vm.Boot.Startup.FindSaved
import OCaml.Vm.Boot.Startup.NameLoop
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Common search prefix, independent of whether the first environment entry is null. -/
structure FindPreludeInput (sp reent name offset env ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 80
  regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)
  saved4 : gprGet c.σ 20 = some s4
  data : EnvName name cs c
  positive : 0 < cs.length
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 80
  environment : bytesT c.σ.mem Layout.sym_environ 8 = env
  nonnull : env ≠ 0#64

def findPreludeRegs (sp reent name offset env s4 : BitVec 64) (count : Nat) : GRegs :=
  [(12, nameCursor name count), (14, 0#64), (15, -61#64), (10, envLockValue false),
   (9, env), (19, BitVec.ofNat 64 Layout.sym_environ), (2, nativeStack sp 80), (18, name),
   (21, reent), (22, offset), (1, jal_80037468_call.link), (20, s4)]

/-- Save, lock, load environ and scan the query name. Both search outcomes
consume this same summary and exact seven-word saved-register log. -/
theorem find_prelude (c : Config) (sp reent name offset env ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (h : FindPreludeInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 9, 10, 12, 14, 15, 18, 19, 21, 22]
        (findLog sp ra s1 s2 s3 s4 s5 s6) c 0x800374a8#64 (envLockValue false)
        (findPreludeRegs sp reent name offset env s4 cs.length)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, locked⟩ := (find_locked c sp reent name offset ra s1 s2 s3 s5 s6 h.toLeafInput h.frame h.regs).run c ⟨pc, rfl⟩
  have dataA := h.data.stack_log h.nameBelow (findPrefix_log_inside h.frame) locked.memory
  have envA : bytesT a.σ.mem Layout.sym_environ 8 = env := by
    rw [locked.memory, native_log_read_below c.σ.mem (findPrefix_log_inside h.frame) ?_]
    · exact h.environment
    · have lower := h.frame.lower
      have below : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
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
  have leafB : LeafInput jal_80037468_call.link b :=
    ⟨started.good, started.image, started.minstret,
      (started.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ locked.regs (by rfl)),
      by decide, started.tick⟩
  obtain ⟨after, run3, scanned⟩ := (name_scan b name _ (envLockValue false) cs dataB h.positive leafB
    (gholds_lookup (n := 12) _ started.regs (by rfl)) started.result).run b ⟨started.pc, rfl⟩
  have effects := ((locked.toEffectPost.trans started.toEffectPost).trans scanned.toEffectPost).widen
    (writes' := [1, 2, 9, 10, 12, 14, 15, 18, 19, 21, 22]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, scanned.memory.trans memoryB, effects.output, effects.frame⟩, ?_⟩⟩
  refine ⟨gholds_lookup (n := 12) _ scanned.regs (by rfl),
    gholds_lookup (n := 14) _ scanned.regs (by rfl), gholds_lookup (n := 15) _ scanned.regs (by rfl), scanned.result,
    (scanned.frame .x9 (by decide) (by decide)).trans (gholds_lookup (n := 9) _ started.regs (by rfl)),
    (scanned.frame .x19 (by decide) (by decide)).trans (gholds_lookup (n := 19) _ started.regs (by rfl)),
    (scanned.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ started.regs (by rfl)),
    (scanned.frame .x18 (by decide) (by decide)).trans (gholds_lookup (n := 18) _ started.regs (by rfl)),
    (scanned.frame .x21 (by decide) (by decide)).trans ((started.frame .x21 (by decide) (by decide)).trans (gholds_lookup (n := 21) _ locked.regs (by rfl))),
    (scanned.frame .x22 (by decide) (by decide)).trans ((started.frame .x22 (by decide) (by decide)).trans (gholds_lookup (n := 22) _ locked.regs (by rfl))),
    (scanned.frame .x1 (by decide) (by decide)).trans leafB.raReg,
    (scanned.frame .x20 (by decide) (by decide)).trans (gholds_lookup (n := 20) _ started.regs (by rfl)), trivial⟩
end OCaml.Vm.Boot.Startup
