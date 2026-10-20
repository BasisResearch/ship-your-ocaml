import OCaml.Vm.Boot.Startup.MemsetWords
import OCaml.Vm.Boot.Startup.PageAddSteps
import OCaml.Vm.Boot.Startup.MemsetTail
import OCaml.Vm.Boot.Startup.MemsetBytes
import OCaml.Vm.Boot.Startup.MemsetShiftHeadNormalized
import OCaml.Vm.Boot.Startup.MemsetShiftHeadImage
import OCaml.Vm.Boot.Startup.MemsetShiftHeadCallInterface
import OCaml.Vm.Boot.Startup.MemsetShiftFixNormalized
import OCaml.Vm.Boot.Startup.MemsetShiftFixImage

/-! newlib's `memset(p, 0, n)` for a pointer eight bytes past a 16-byte
boundary (`p ≡ 8 mod 16`) and `n ≡ 0 mod 16`: the misaligned head stores eight
bytes through a computed call into the byte table, the fixup re-enters the
aligned path at `p + 8`, the pair loop clears `(n - 16) / 16` pairs, and the
computed tail stores the last eight bytes. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- `clearWords` as one write log. -/
def clearLog (base : Nat) : Nat → List WEntry
  | 0 => []
  | n + 1 => clearLog base n ++ [(base + 8 * n, 8, 0#64)]

theorem clearWords_log (m : Std.ExtHashMap Nat (BitVec 8)) (base : Nat) :
    ∀ n, clearWords m base n = writeLog m (clearLog base n)
  | 0 => rfl
  | n + 1 => by rw [clearWords, clearLog, writeLog_append, clearWords_log m base n]

theorem shifted_mask16 {p : BitVec 64} (shifted : p.toNat % 16 = 8) :
    p &&& Functions.sign_extend (m := 64) 0x00f#12 = 8#64 := by
  rw [show Functions.sign_extend (m := 64) 0x00f#12 = 15#64 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2^4 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
  exact shifted

theorem big_guard {n : BitVec 64} (big : 16 ≤ n.toNat) :
    guardB bop.BGEU (0#64 + Functions.sign_extend (m := 64) 15#12) n = false := by
  rw [show 0#64 + Functions.sign_extend (m := 64) 15#12 = 15#64 by decide]
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_le.mp hc) (by simp only [BitVec.toNat_ofNat]; omega))

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

def memsetShiftEntryBlocks : List BBlock := memsetX276cFSeg ++ memsetX2778TSeg

/-- The entry checks on a shifted pointer branch to the misaligned head. -/
theorem memset_shift_entry (c : Config) (p n ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, p), (11, 0#64), (12, n)]) (shifted : p.toNat % 16 = 8) (big : 16 ≤ n.toNat) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [6, 14, 15] c ra 0x8004281c#64 [(15, 8#64), (14, p), (6, 15#64), (10, p), (11, 0#64), (12, n)]) := by
  have mask := shifted_mask16 shifted
  have input : BlockInput memsetShiftEntryBlocks 0x8004276c#64 [(10, p), (11, 0#64), (12, n)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [10, 11, 12]; decide
    shape := by change ChainOK _ [10, 11, 12] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetPrefix_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals simp only [memsetprefix_line_8004276c, memsetprefix_line_80042770, memsetprefix_line_80042778, runGM,
        stepGM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, zero_imm, BitVec.add_zero, Nat.reduceEqDiff,
        ite_true, ite_false]
      all_goals try rw [mask]
      all_goals first | exact big_guard big | decide }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetShiftEntryBlocks, memsetX276cFSeg, memsetX2778TSeg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetprefix_line_8004276c, memsetprefix_line_80042770, memsetprefix_line_80042778,
      runGM, stepGM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, zero_imm, BitVec.add_zero,
      Nat.reduceEqDiff, ite_true, ite_false] at pins
    rw [mask] at pins
    exact ⟨gholds_lookup_eq pins rfl rfl, gholds_lookup (n := 14) _ pins rfl, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, trivial⟩
  · decide
  · decide

/-- The head computes the byte-table entry for an eight-byte head and keeps `ra` in `t0`. -/
theorem memset_shift_head (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(15, 8#64), (1, ra)]) :
    FnSummary 0x8004281c#64 (fun d => d = c)
      (BoundaryPost [13, 5] c ra 0x8004282c#64 [(13, 0x80042840#64), (5, ra), (15, 8#64), (1, ra)]) := by
  have input : BlockInput memsetX281cSeg 0x8004281c#64 [(15, 8#64), (1, ra)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [15, 1]; decide
    shape := by change ChainOK _ [15, 1] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetShiftHead_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_" }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetX281cSeg, evalBlocks, evalBlock, SegEvalState.init, memsetshifthead_line_8004281c,
      memsetshifthead_line_80042820, memsetshifthead_line_80042824, memsetshifthead_line_80042828, runGM, stepGM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by rw [zero_imm, BitVec.add_zero]),
      gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 1) _ pins rfl, trivial⟩
  · decide
  · decide

theorem shift_minus : 8#64 + Functions.sign_extend (m := 64) 0xff0#12 = -8#64 := by decide

theorem fix_guard {n : BitVec 64} (big : 32 ≤ n.toNat) :
    guardB bop.BGEU 15#64 (n + -8#64) = false := by
  unfold guardB Functions.zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  rw [← BitVec.sub_eq_add_neg]
  have sub : (n - 8#64).toNat = n.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega)]; rfl
  exact decide_eq_false (by intro hc; rw [sub] at hc; exact absurd (Int.ofNat_le.mp hc) (by simp only [BitVec.toNat_ofNat]; omega))

def memsetShiftFixBlocks : List BBlock := memsetX2830FSeg ++ memsetX2844Seg

/-- The fixup restores `ra` and re-enters the aligned path at `p + 8` with `n - 8` bytes. -/
theorem memset_shift_fix (c : Config) (p n ra : BitVec 64) (leaf : LeafInput 0x80042830#64 c)
    (regs : GHolds c.σ [(5, ra), (15, 8#64), (14, p), (12, n), (6, 15#64), (10, p)]) (big : 32 ≤ n.toNat) :
    FnSummary 0x80042830#64 (fun d => d = c)
      (WriteRegistersPost [1, 15, 14, 12] [] c 0x80042780#64 p [(1, ra), (15, -8#64), (14, p - -8#64), (12, n + -8#64),
        (5, ra), (6, 15#64), (10, p)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput memsetShiftFixBlocks 0x80042830#64
        [(5, ra), (15, 8#64), (14, p), (12, n), (6, 15#64), (10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [5, 15, 14, 12, 6, 10]; decide
      shape := by change ChainOK _ [5, 15, 14, 12, 6, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := memsetShiftFix_code leaf.image
        chain_facts code with "Vsa.Sim.Code.memset_at_"
        all_goals simp only [memsetshiftfix_line_80042830, memsetshiftfix_line_80042834, memsetshiftfix_line_80042838,
          memsetshiftfix_line_8004283c, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some,
          Nat.reduceEqDiff, ite_true, ite_false, zero_imm, BitVec.add_zero, shift_minus]
        all_goals first | exact fix_guard big | decide }))
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetShiftFixBlocks, memsetX2830FSeg, memsetX2844Seg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetshiftfix_line_80042830, memsetshiftfix_line_80042834,
      memsetshiftfix_line_80042838, memsetshiftfix_line_8004283c, runGM, stepGM, srcVal, lookupG, eraseG, wvalM,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, zero_imm, BitVec.add_zero, shift_minus] at pins
    exact ⟨gholds_lookup (n := 1) _ pins rfl, gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 14) _ pins rfl,
      gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 5) _ pins rfl, gholds_lookup (n := 6) _ pins rfl,
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

def memsetRealignBlocks : List BBlock := memsetX2780FSeg ++ memsetX2784Seg

/-- Re-entry at the aligned path: the pair limit and the remainder. -/
theorem memset_realign (c : Config) (b m ra v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, 0#64), (12, m), (14, b), (10, v)]) :
    FnSummary 0x80042780#64 (fun d => d = c)
      (BoundaryPost [13, 12] c ra 0x80042790#64 [(13, (m &&& Functions.sign_extend (m := 64) 0xff0#12) + b),
        (12, m &&& Functions.sign_extend (m := 64) 0x00f#12), (11, 0#64), (14, b), (10, v)]) := by
  have input : BlockInput memsetRealignBlocks 0x80042780#64 [(11, 0#64), (12, m), (14, b), (10, v)] [] c := {
    good := leaf.good
    minstret := leaf.minstret
    regs := regs
    keys := by change KeysOK [11, 12, 14, 10]; decide
    shape := by change ChainOK _ [11, 12, 14, 10] _; decide
    tick := leaf.tick
    facts := by
      have code := memsetPrefix_code leaf.image
      chain_facts code with "Vsa.Sim.Code.memset_at_"
      all_goals simp only [srcVal, lookupG, runGM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
      all_goals decide }
  apply boundary_of_blocks leaf (block_summary _ _ _ _ _ input)
  · rfl
  · rfl
  · intro σ pins
    simp only [memsetRealignBlocks, memsetX2780FSeg, memsetX2784Seg, List.cons_append, List.nil_append, evalBlocks,
      evalBlock, SegEvalState.init, memsetprefix_line_80042784, memsetprefix_line_80042788, memsetprefix_line_8004278c,
      runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false] at pins
    exact ⟨gholds_lookup (n := 13) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 11) _ pins rfl,
      gholds_lookup (n := 14) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · decide
  · decide

end OCaml.Vm.Boot.Startup
