import OCaml.Vm.Boot.Startup.FindPrelude
import OCaml.Vm.Boot.Startup.FindSearchMemory
import OCaml.Vm.Boot.Startup.FoundTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

structure FindPresentInput (sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (byte : Nat → BitVec 8) (c : Config) : Prop
    extends FindPreludeInput sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs c where
  search : SearchEntry sp env entry name cs.length byte c
  saved0 : gprGet c.σ 8 = some s0
  slot : WriteWindow offset 4
  offsetHigh : sp.toNat ≤ offset.toNat
  storesOutside : ImageOutside (findFoundLog sp (nameCursor entry cs.length) offset)

def findPresentLog (sp ra s0 s1 s2 s3 s4 s5 s6 pointer offset : BitVec 64) : List WEntry :=
  findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6 ++ findFoundLog sp pointer offset

def findPresentRegs (sp ra s0 s1 s2 s3 s4 s5 s6 env entry name : BitVec 64) (count : Nat) : GRegs :=
  (findFoundReturnRegs sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry count) ++ [(14, env)]) ++
    [(11, nameCursor name count), (12, nameCursor entry (count - 1))]

/-- Complete _findenv_r for a matching first environment entry. This uses the
native bounded-comparison loop and returns its value pointer after restoring
the caller, recording index zero and releasing the environment lock. -/
theorem findenv_present (c : Config) (sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 : BitVec 64)
    (cs : List Char) (byte : Nat → BitVec 8)
    (h : FindPresentInput sp reent name offset env entry ra s0 s1 s2 s3 s4 s5 s6 cs byte c) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
        (findPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry cs.length) offset)
        c ra (nameCursor entry cs.length + 1#64)
        (findPresentRegs sp ra s0 s1 s2 s3 s4 s5 s6 env entry name cs.length)) := by
  constructor
  rintro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, prepared⟩ := (find_prelude c sp reent name offset env ra s1 s2 s3 s4 s5 s6 cs h.toFindPreludeInput).run c ⟨pc, rfl⟩
  have dataA := h.search.stack_log (findLog_inside h.frame) prepared.memory
  have regsA : GHolds a.σ (findMatchedInput sp s0 env name cs.length) :=
    ⟨gholds_lookup (n := 9) _ prepared.regs (by rfl), gholds_lookup (n := 14) _ prepared.regs (by rfl),
      gholds_lookup (n := 2) _ prepared.regs (by rfl), (prepared.frame .x8 (by decide) (by decide)).trans h.saved0,
      gholds_lookup (n := 12) _ prepared.regs (by rfl), gholds_lookup (n := 18) _ prepared.regs (by rfl), trivial⟩
  obtain ⟨b, run2, matched⟩ := (find_matched a sp s0 env name entry _ cs.length byte
    (prepared.leaf (by rfl) (by decide)) dataA regsA).run a ⟨prepared.pc, rfl⟩
  have memoryB : b.σ.mem = writeLog c.σ.mem (findSearchLog sp ra s0 s1 s2 s3 s4 s5 s6) := by
    rw [matched.memory, prepared.memory, findSearchLog_eq, writeLog_append]
  have envB : bytesT b.σ.mem Layout.sym_environ 8 = env := by
    rw [memoryB, native_log_read_below c.σ.mem (findSearchLog_inside h.frame) ?_]
    · exact h.environment
    · have lower := h.frame.lower
      have global : Layout.sym_environ + 8 ≤ DlHeap.heapEnd := by decide
      unfold nativeFrameBase
      omega
  obtain ⟨saved, saved4, saved0⟩ := findSearch_saved h.frame memoryB
  have regsB : GHolds b.σ (findFoundInput sp env reent (nameCursor entry cs.length) offset) :=
    ⟨(matched.frame .x19 (by decide) (by decide)).trans (gholds_lookup (n := 19) _ prepared.regs (by rfl)),
      (matched.frame .x21 (by decide) (by decide)).trans (gholds_lookup (n := 21) _ prepared.regs (by rfl)),
      gholds_lookup (n := 15) _ matched.regs (by rfl), gholds_lookup (n := 9) _ matched.regs (by rfl),
      (matched.frame .x22 (by decide) (by decide)).trans (gholds_lookup (n := 22) _ prepared.regs (by rfl)),
      gholds_lookup (n := 2) _ matched.regs (by rfl), trivial⟩
  obtain ⟨after, run3, returned⟩ := (find_found_tail b sp env reent (nameCursor entry cs.length) offset ra _ s0 s1 s2 s3 s4 s5 s6
    (matched.leaf (by rfl) (by decide)) h.frame regsB envB h.slot h.offsetHigh h.storesOutside
    saved saved0 saved4 h.aligned).run b ⟨matched.pc, rfl⟩
  have effects := ((prepared.toEffectPost.trans matched.toEffectPost).trans returned.toEffectPost).widen
    (writes' := [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]) (by decide)
  refine ⟨after, run1.trans (run2.trans run3), ⟨⟨effects.good, effects.image, effects.minstret, effects.tick,
    effects.pc, effects.result, ?_, effects.output, effects.frame⟩, ?_⟩⟩
  · rw [returned.memory, memoryB, findPresentLog, writeLog_append]
  · apply (gholds_append _ _).mpr
    exact ⟨returned.regs,
      (returned.frame .x11 (by decide) (by decide)).trans (gholds_lookup (n := 11) _ matched.regs (by rfl)),
      (returned.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ matched.regs (by rfl)), trivial⟩
end OCaml.Vm.Boot.Startup
