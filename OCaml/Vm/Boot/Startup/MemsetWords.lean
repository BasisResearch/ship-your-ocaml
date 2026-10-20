import OCaml.Vm.Primitives.LibraryEffects
import OCaml.Vm.Primitives.RegisterPins
import OCaml.Vm.Boot.Startup.MemsetLoop
import OCaml.Vm.Boot.Startup.MemsetTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap LeanRV64DExecutable OCaml.Vm.Primitives

/-! `memset(p, 0, 16 * count)` on an aligned arena extent: the entry checks,
`count` word pairs, and the return with no remainder. -/

/-- No remainder bytes: return. -/
theorem memset_exit (c : Config) (ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(12, 0#64), (10, v), (1, ra)]) :
    FnSummary 0x800427a0#64 (fun d => d = c) (WriteRegistersPost [] [] c ra v [(12, 0#64), (10, v), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (memsetX27a0FSeg ++ memsetX27a4Seg) 0x800427a0#64
        [(12, 0#64), (10, v), (1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [12, 10, 1]; decide
      shape := by change ChainOK _ [12, 10, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := memsetPrefix_code leaf.image
        chain_facts code with "Vsa.Sim.Code.memset_at_"
        · rfl
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    exact ret_tgt ra leaf.aligned
  · rfl
  · rfl
  · decide

def memsetWordsRegs (base count : Nat) : GRegs :=
  [(6, 15#64), (12, 0#64), (15, 0#64), (13, pairCursor base count), (14, pairCursor base count),
    (10, BitVec.ofNat 64 base)]

/-- `memset(base, 0, n)` with `n = 16 * count`: the extent's words cleared. -/
theorem memset_words (c : Config) (base count : Nat) (n ra : BitVec 64) (region : ZeroPairRegion base count)
    (pos : 0 < count) (h : MemsetInput (BitVec.ofNat 64 base) n ra c)
    (limit : n &&& Functions.sign_extend (m := 64) 0xff0#12 = BitVec.ofNat 64 (16 * count))
    (rem : n &&& Functions.sign_extend (m := 64) 0x00f#12 = 0#64) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (RegistersPost [6, 14, 15, 13, 12] (clearWords c.σ.mem base (2 * count)) c ra (BitVec.ofNat 64 base)
        (memsetWordsRegs base count)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, front, frontPost⟩ := (memset_prefix c _ n ra h).run c ⟨pc, rfl⟩
  have regsA := frontPost.regs
  simp only [memsetPrefixRegsN, limit, rem] at regsA
  have entry : ZeroPairsAt base count 0 ra (BitVec.ofNat 64 base) a a := {
    leaf := frontPost.toLeafInput
    bound := by omega
    pc := by simp only [pos, ite_true]; exact frontPost.pc
    destination := gholds_lookup (n := 10) _ regsA rfl
    zero := gholds_lookup (n := 11) _ regsA rfl
    cursor := gholds_lookup (n := 14) _ regsA rfl
    limitReg := by
      have v := gholds_lookup (n := 13) _ regsA rfl
      have addr : BitVec.ofNat 64 (16 * count) + BitVec.ofNat 64 base = pairCursor base count := by
        simp only [pairCursor, ← BitVec.ofNat_add]
        congr 1; omega
      rw [addr] at v
      exact v
    memory := rfl
    output := rfl
    frame := fun _ _ _ => rfl }
  obtain ⟨b, loop, pairs⟩ := zero_pairs region.span a a entry
  have pcB : PCAt 0x800427a0#64 b := by have := pairs.pc; simp only [Nat.lt_irrefl, ite_false] at this; exact this
  obtain ⟨d, exitRun, post⟩ := (memset_exit b ra (BitVec.ofNat 64 base) pairs.leaf
    ⟨(pairs.frame .x12 (by decide) (by decide)).trans (gholds_lookup (n := 12) _ regsA rfl), pairs.destination,
      pairs.leaf.raReg, trivial⟩).run b ⟨pcB, rfl⟩
  have pairsKept : GprsKept a b :=
    GprsKept.of_regFrame (W := [14]) (by decide) (by decide)
      (fun n hn => by rw [List.mem_singleton.mp hn, pairs.cursor]; rfl) pairs.frame
  refine ⟨d, front.trans (loop.trans exitRun), ?_, ?_⟩
  · have kept := frontPost.kept.trans (pairsKept.trans post.kept)
    refine { post.toEffectPost with memory := ?_, output := ?_, frame := ?_, kept := kept }
    · rw [post.memory, pairs.memory, frontPost.memory]; rfl
    · exact post.output.trans (pairs.output.trans frontPost.output)
    · have loopIncl : ∀ n ∈ [14], n ∈ [6, 14, 15, 13, 12] := by decide
      intro r outside noise
      exact (post.frame r (by simp) noise).trans ((pairs.frame r (fun n hn => outside n (loopIncl n hn)) noise).trans
        (frontPost.frame r outside noise))
  · have toD (n : Nat) (lo : 1 ≤ n) (hi : n ≤ 31) : gprGet d.σ n = gprGet b.σ n :=
      post.toEffectPost.gpr_frame (by decide) n lo hi (by simp)
    exact ⟨(toD 6 (by decide) (by decide)).trans ((pairs.frame .x6 (by decide) (by decide)).trans
        (gholds_lookup (n := 6) _ regsA rfl)),
      (toD 12 (by decide) (by decide)).trans ((pairs.frame .x12 (by decide) (by decide)).trans
        (gholds_lookup (n := 12) _ regsA rfl)),
      (toD 15 (by decide) (by decide)).trans ((pairs.frame .x15 (by decide) (by decide)).trans
        (gholds_lookup (n := 15) _ regsA rfl)),
      (toD 13 (by decide) (by decide)).trans pairs.limitReg, (toD 14 (by decide) (by decide)).trans pairs.cursor,
      (toD 10 (by decide) (by decide)).trans pairs.destination, trivial⟩
end OCaml.Vm.Boot.Startup
