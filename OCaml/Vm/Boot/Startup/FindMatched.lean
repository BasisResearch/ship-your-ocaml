import OCaml.Vm.Boot.Startup.SearchEntry
import OCaml.Vm.Boot.Startup.FindLoaded
import OCaml.Vm.Boot.Startup.FindCompared
import OCaml.Vm.Boot.Startup.FindMatch
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def findMatchedInput (sp s0 env name : BitVec 64) (count : Nat) : GRegs :=
  [(9, env), (14, 0#64), (2, nativeStack sp 80), (8, s0), (12, nameCursor name count), (18, name)]
def findMatchedRegs (sp env name entry : BitVec 64) (count : Nat) : GRegs :=
  findMatchRegs env entry (BitVec.ofNat 64 count) ++
    [(11, nameCursor name count), (12, nameCursor entry (count - 1)), (2, nativeStack sp 80),
     (18, name), (1, jal_800374c8_call.link)]

/-- Inspect the first entry, call strncmp and check its equals delimiter. The
name scan is already complete; this summary reaches the successful tail. -/
theorem find_matched (c : Config) (sp s0 env name entry ra : BitVec 64) (count : Nat) (byte : Nat → BitVec 8)
    (leaf : LeafInput ra c) (data : SearchEntry sp env entry name count byte c)
    (regs : GHolds c.σ (findMatchedInput sp s0 env name count)) :
    FnSummary 0x800374a8#64 (fun d => d = c)
      (WriteRegistersPost [20, 10, 8, 12, 11, 1, 14, 15] (findCompareLog sp s0) c 0x80037520#64 0#64
        (findMatchedRegs sp env name entry count)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, loaded⟩ := (find_loaded c env entry ra leaf
    ⟨regs.1, regs.2.1, trivial⟩ data.array data.first data.nonnull).run c ⟨pc, rfl⟩
  have leafA : LeafInput ra a := ⟨loaded.good, loaded.image, loaded.minstret,
    (loaded.frame .x1 (by decide) (by decide)).trans leaf.raReg, leaf.aligned, loaded.tick⟩
  have regsA : GHolds a.σ (findCompareInput sp s0 name (nameCursor name count) entry) := ⟨
    (loaded.frame .x2 (by decide) (by decide)).trans regs.2.2.1,
    (loaded.frame .x8 (by decide) (by decide)).trans regs.2.2.2.1,
    (loaded.frame .x12 (by decide) (by decide)).trans regs.2.2.2.2.1,
    (loaded.frame .x18 (by decide) (by decide)).trans regs.2.2.2.2.2.1, loaded.result, trivial⟩
  have dataA := data.same_mem loaded.memory
  obtain ⟨b, run2, compared⟩ := (find_compared a sp s0 name entry ra count byte leafA data.frame regsA
    data.positive data.small dataA.comparison (by have := data.entryBelow; omega) data.nameBelow data.unaligned).run a ⟨loaded.pc, rfl⟩
  have dataB := dataA.stack_log (findCompareLog_inside data.frame) compared.memory
  have envB : gprGet b.σ 9 = some env :=
    (compared.frame .x9 (by decide) (by decide)).trans (gholds_lookup (n := 9) _ loaded.regs (by rfl))
  have delimiter : gprGet b.σ 20 = some 61#64 :=
    (compared.frame .x20 (by decide) (by decide)).trans (gholds_lookup (n := 20) _ loaded.regs (by rfl))
  have regsB : GHolds b.σ (findMatchInput env (BitVec.ofNat 64 count)) :=
    ⟨compared.result, envB, gholds_lookup (n := 8) _ compared.regs (by rfl), delimiter, trivial⟩
  obtain ⟨after, run3, matched⟩ := (find_match b env entry _ _ (compared.leaf (by rfl) (by decide)) regsB data.array dataB.first
    (name_window data.region (Nat.le_refl _)) dataB.equals).run b ⟨compared.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (findCompareLog sp s0) := by
    have same : a.σ.mem = c.σ.mem := loaded.memory
    rw [compared.memory, same]
  have effects := ((loaded.toEffectPost.trans compared.toEffectPost).trans matched.toEffectPost).widen
    (writes' := [20, 10, 8, 12, 11, 1, 14, 15]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, matched.memory.trans memoryB, effects.output, effects.frame⟩, ?_⟩⟩
  apply (gholds_append _ _).mpr
  refine ⟨matched.regs, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · have cursor := gholds_lookup (n := 11) _ compared.regs (by rfl)
    have length : count - 1 + 1 = count := by have := data.positive; omega
    rw [length] at cursor
    exact (matched.frame .x11 (by decide) (by decide)).trans cursor
  · exact (matched.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ compared.regs (by rfl))
  · exact (matched.frame .x2 (by decide) (by decide)).trans (gholds_lookup (n := 2) _ compared.regs (by rfl))
  · exact (matched.frame .x18 (by decide) (by decide)).trans (gholds_lookup (n := 18) _ compared.regs (by rfl))
  · exact (matched.frame .x1 (by decide) (by decide)).trans (gholds_lookup (n := 1) _ compared.regs (by rfl))
end OCaml.Vm.Boot.Startup
