import OCaml.Vm.Boot.Startup.FindPrelude
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
    (cs : List Char) (c : Config) : Prop extends LeafInput ra c, EmptyEnvironment sp 80 env c where
  regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)
  saved4 : gprGet c.σ 20 = some s4
  data : EnvName name cs c
  positive : 0 < cs.length
  nameBelow : name.toNat + cs.length + 1 ≤ nativeFrameBase sp 80

/-- Complete `_findenv_r` for an empty environment: save, lock, scan, inspect
the null first entry, unlock, restore and return null. -/
theorem findenv_empty (c : Config) (sp reent name offset env ra s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (h : FindEnvInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 9, 10, 12, 14, 15, 18, 19, 20, 21, 22]
        (findLog sp ra s1 s2 s3 s4 s5 s6) c ra 0#64
        (findEnvRegs sp ra s1 s2 s3 s4 s5 s6 name cs.length)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  have input : FindPreludeInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c := {
    toLeafInput := h.toLeafInput
    frame := h.frame
    regs := h.regs
    saved4 := h.saved4
    data := h.data
    positive := h.positive
    nameBelow := h.nameBelow
    environment := h.environment
    nonnull := h.nonnull }
  obtain ⟨a, run1, prepared⟩ := (find_prelude c sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs input).run c ⟨pc, rfl⟩
  have envA := h.toEmptyEnvironment.stack_log (findLog_inside h.frame) prepared.memory
  have regsA : GHolds a.σ (findEmptyInput env) :=
    ⟨gholds_lookup (n := 9) _ prepared.regs (by rfl), gholds_lookup (n := 14) _ prepared.regs (by rfl), trivial⟩
  have leafA := prepared.leaf (ra := jal_80037468_call.link) (by rfl) (by decide)
  obtain ⟨b, run2, missing⟩ := (find_empty a env _ leafA regsA h.envWindow envA.empty).run a ⟨prepared.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (findLog sp ra s1 s2 s3 s4 s5 s6) := missing.memory.trans prepared.memory
  obtain ⟨saved, saved4⟩ := find_saved h.frame memoryB
  have leafB : LeafInput jal_80037468_call.link b :=
    ⟨missing.good, missing.image, missing.minstret,
      (missing.frame .x1 (by decide) (by decide)).trans leafA.raReg, by decide, missing.tick⟩
  have regsB : GHolds b.σ (findRestoreInput sp reent) := ⟨
    (missing.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ prepared.regs (by rfl)),
    (missing.frame .x21 (by decide) (by decide)).trans (gholds_lookup (n := 21) _ prepared.regs (by rfl)), missing.result, trivial⟩
  obtain ⟨after, run3, post⟩ := (find_tail b sp reent ra s1 s2 s3 s4 s5 s6 _ leafB h.frame regsB saved4 saved h.aligned).run b ⟨missing.pc, rfl⟩
  have effects := ((prepared.toEffectPost.trans missing.toEffectPost).trans post.toEffectPost).widen
    (writes' := [1, 2, 9, 10, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, post.memory.trans memoryB, effects.output, effects.frame⟩, ?_⟩⟩
  apply (gholds_append _ _).mpr
  exact ⟨post.regs,
    (post.frame .x12 (by decide) (by decide)).trans ((missing.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ prepared.regs (by rfl))),
    (post.frame .x14 (by decide) (by decide)).trans (gholds_lookup (n := 14) _ missing.regs (by rfl)),
    (post.frame .x15 (by decide) (by decide)).trans ((missing.frame .x15 (by decide) (by decide)).trans (gholds_lookup (n := 15) _ prepared.regs (by rfl))), trivial⟩
end OCaml.Vm.Boot.Startup
