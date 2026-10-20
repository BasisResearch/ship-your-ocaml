import OCaml.Vm.Boot.Startup.InitMergeEntryNormalized
import OCaml.Vm.Boot.Startup.InitMergeEntryImage
import OCaml.Vm.Boot.Startup.InitMergeHeadNormalized
import OCaml.Vm.Boot.Startup.InitMergeHeadImage
import OCaml.Vm.Boot.Startup.InitMergeEmptyNormalized
import OCaml.Vm.Boot.Startup.InitMergeEmptyImage
import OCaml.Vm.Boot.Startup.InitMergeTailNormalized
import OCaml.Vm.Boot.Startup.InitMergeTailImage
import OCaml.Vm.Boot.Startup.PageAddSteps
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! bf_init_merge on a heap whose 16 small free lists are empty: each list
becomes `{free = NULL, merge = &free}` and its bit leaves `bf_small_map`. -/

local macro "imk" : tactic => `(tactic| simp only [initmergeentry_line_800061a0, initmergeentry_line_800061a4, initmergeentry_line_800061a8, initmergeentry_line_800061ac, initmergeentry_line_800061b0, initmergeentry_line_800061b4, initmergeentry_line_800061b8, initmergeentry_line_800061bc, initmergeentry_line_800061c0, initmergeentry_line_800061c4, initmergeentry_line_800061c8, initmergeentry_line_800061cc, initmergeentry_line_800061d0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `bf_small_map`. -/
def smallMapAddr : Nat := 0x80064a00

/-- `caml_fl_merge := NULL`; the loop over `bf_small_fl[1..16]` starts. -/
theorem init_merge_entry (c : Config) (ra v map : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, v)])
    (small : bytesVal .lw (read4 c.σ.mem smallMapAddr) = map) :
    FnSummary 0x800061a0#64 (fun e => e = c) (WriteRegistersPost [6, 15, 16, 17, 29, 11, 10, 30, 28]
      [(0x80064a38, 8, 0#64)] c 0x800061d4#64 512#64
      [(6, map), (15, 0x800651a8#64), (16, 0x800662e8#64), (17, 0#64), (29, 0#64), (11, 0x80064a40#64),
        (10, 512#64), (30, 1#64), (28, 16#64)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput bf_init_mergeX61a0Seg 0x800061a0#64 [(10, v)]
        [read4 c.σ.mem smallMapAddr] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := initMergeEntry_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_init_merge_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 smallMapAddr) 4 by constructor <;> decide).lw rfl (by imk; decide)
            (read4_pins _ _)
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064a38) 8 by constructor <;> decide).sd rfl (by imk; decide) }))
  · simp only [bf_init_mergeX61a0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, wlogM,
      wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, imm20Of, initmergeentry_line_800061a0, initmergeentry_line_800061a4, initmergeentry_line_800061a8, initmergeentry_line_800061ac, initmergeentry_line_800061b0, initmergeentry_line_800061b4, initmergeentry_line_800061b8, initmergeentry_line_800061bc, initmergeentry_line_800061c0, initmergeentry_line_800061c4, initmergeentry_line_800061c8, initmergeentry_line_800061cc, initmergeentry_line_800061d0]
    decide
  · rfl
  · intro σ pins
    simp only [bf_init_mergeX61a0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, srcVal,
      lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons, List.tail_cons,
      imm20Of, initmergeentry_line_800061a0, initmergeentry_line_800061a4, initmergeentry_line_800061a8, initmergeentry_line_800061ac, initmergeentry_line_800061b0, initmergeentry_line_800061b4, initmergeentry_line_800061b8, initmergeentry_line_800061bc, initmergeentry_line_800061c0, initmergeentry_line_800061c4, initmergeentry_line_800061c8, initmergeentry_line_800061cc, initmergeentry_line_800061d0] at pins
    exact ⟨gholds_lookup_eq pins rfl small, gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      trivial⟩
  · rfl
  · decide

/-- `bf_small_fl[k + 1]`'s record. -/
def smallList (k : Nat) : BitVec 64 := 0x800662e8#64 + BitVec.ofNat 64 (16 * k)

theorem smallList_nat (k : Nat) (hk : k < 16) (off : Nat) (h : off ≤ 8) :
    (smallList k + BitVec.ofNat 64 off).toNat = 0x800662e8 + 16 * k + off := by
  unfold smallList
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem smallList_window (k : Nat) (hk : k < 16) (off : Nat) (h : off ≤ 8) (al : off % 8 = 0) :
    WriteWindow (smallList k + BitVec.ofNat 64 off) 8 := by
  have n := smallList_nat k hk off h
  have hT : Layout.sym_tohost = 0x80061fc0 := rfl
  constructor <;> (try rw [hT]) <;> rw [n] <;> omega

theorem smallList_read (k : Nat) (hk : k < 16) : ReadWindow (smallList k) 8 := by
  have w := smallList_window k hk 0 (by decide) (by decide)
  rw [show smallList k + BitVec.ofNat 64 0 = smallList k by simp] at w
  exact ⟨w.lower, w.upper, Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide) _) w.htif)⟩

theorem init_merge_count : ∀ k, k < 16 →
    guardB bop.BNE (BitVec.ofNat 64 k + Functions.sign_extend (m := 64) 1#12) 16#64 = decide (k + 1 < 16) := by
  decide

/-- The bits from `k` up. -/
def clearLow (k : Nat) : BitVec 64 := ~~~((1#64 <<< k) - 1#64)

theorem small_bit : ∀ k, k < 16 →
    Functions.sign_extend (m := 64) (Sail.shift_bits_left (Sail.BitVec.extractLsb (1#64) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 k) 31 0) 4 0)) ^^^
      Functions.sign_extend (m := 64) 4095#12 = ~~~(1#64 <<< k) := by
  decide

theorem clearLow_succ : ∀ k, k < 16 → clearLow k &&& ~~~(1#64 <<< k) = clearLow (k + 1) := by
  decide

/-- The list record's `free` and `merge`. -/
def smallListLog (k : Nat) : List WEntry :=
  [((smallList k).toNat, 8, 0#64), ((smallList k + 8#64).toNat, 8, smallList k)]

theorem smallListLog_outside (k : Nat) (hk : k < 16) : ImageOutside (smallListLog k) := by
  have a0 := smallList_nat k hk 0 (by decide)
  have a8 := smallList_nat k hk 8 (by decide)
  rw [show smallList k + BitVec.ofNat 64 0 = smallList k by simp] at a0
  constructor <;> simp only [smallListLog, OutLRange, a0, show smallList k + 8#64 = smallList k + BitVec.ofNat 64 8 from rfl,
    a8, and_true] <;> simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega

local macro "imh" : tactic => `(tactic| simp only [initmergehead_line_800061d4, initmergeempty_line_8000622c, initmergeempty_line_80006230, initmergeempty_line_80006234, initmergeempty_line_80006238, initmergeempty_line_8000623c, initmergeempty_line_80006240, initmergeempty_line_80006244, initmergeempty_line_80006248, initmergeempty_line_8000624c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

def initMergeBlocks (more : Bool) : List BBlock :=
  bf_init_mergeX61d4TSeg ++ if more then bf_init_mergeX622cTSeg else bf_init_mergeX622cFSeg

theorem init_merge_step (c : Config) (ra t1 : BitVec 64) (k : Nat) (lt : k < 16) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(16, smallList k), (17, BitVec.ofNat 64 k), (6, t1), (30, 1#64), (28, 16#64), (10, 512#64)])
    (empty : bytesT c.σ.mem (smallList k).toNat 8 = 0#64) :
    FnSummary 0x800061d4#64 (fun e => e = c) (WriteRegistersPost [13, 15, 17, 6, 29, 16] (smallListLog k) c
      (if k + 1 < 16 then 0x800061d4#64 else 0x80006254#64) 512#64
      [(16, smallList (k + 1)), (17, BitVec.ofNat 64 (k + 1)), (6, t1 &&& ~~~(1#64 <<< k)), (29, 1#64),
        (13, 0#64), (15, ~~~(1#64 <<< k)), (30, 1#64), (28, 16#64), (10, 512#64)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (smallList k).toNat) = 0#64 := by rw [read8_value]; exact empty
  have count := init_merge_count k lt
  have bit := small_bit k lt
  have next : smallList k + Functions.sign_extend (m := 64) 16#12 = smallList (k + 1) := by
    unfold smallList
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  have succ : BitVec.ofNat 64 k + Functions.sign_extend (m := 64) 1#12 = BitVec.ofNat 64 (k + 1) := by
    rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, ← BitVec.ofNat_add]
  apply registers_of_blocks' (keys := by unfold initMergeBlocks; split <;> decide)
    (no3 := by unfold initMergeBlocks; split <;> decide) leaf.image (smallListLog_outside k lt)
    (block_summary _ _ _ _ _ (show BlockInput (initMergeBlocks (decide (k + 1 < 16))) 0x800061d4#64
        [(16, smallList k), (17, BitVec.ofNat 64 k), (6, t1), (30, 1#64), (28, 16#64), (10, 512#64)]
        [read8 c.σ.mem (smallList k).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [16, 17, 6, 30, 28, 10]; decide
      shape := by unfold initMergeBlocks; split <;> (change ChainOK _ [16, 17, 6, 30, 28, 10] _; decide)
      tick := leaf.tick
      facts := by
        have code := initMergeHead_code leaf.image
        unfold initMergeBlocks
        split
        all_goals chain_facts code with "Vsa.Sim.Code.bf_init_merge_at_"
        all_goals imh
        all_goals first
          | exact (smallList_read k lt).ld rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sext_zero, BitVec.add_zero]) (read8_pins _ _)
          | (rw [word]; rfl)
          | exact (smallList_window k lt 0 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sext_zero, BitVec.add_zero]; exact (BitVec.add_zero _).symm)
          | exact (smallList_window k lt 8 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, sext_zero, BitVec.add_zero]; rfl)
          | (rw [count]; simp_all)
          | exact (smallList_window k lt 0 (by decide) (by decide)).sd rfl (by simp only [eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; rw [sext_zero]) }))
  · unfold initMergeBlocks
    split <;> simp only [bf_init_mergeX61d4TSeg, bf_init_mergeX622cTSeg, bf_init_mergeX622cFSeg, List.cons_append,
      List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, wlogM, wentryM,
      widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.headD_cons, List.tail_cons, initmergehead_line_800061d4, initmergeempty_line_8000622c, initmergeempty_line_80006230, initmergeempty_line_80006234, initmergeempty_line_80006238, initmergeempty_line_8000623c, initmergeempty_line_80006240, initmergeempty_line_80006244, initmergeempty_line_80006248, initmergeempty_line_8000624c] <;>
      rw [sext_zero, BitVec.add_zero, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide] <;> rfl
  · unfold initMergeBlocks
    by_cases more : k + 1 < 16
    · simp only [more, decide_true, ite_true]; rfl
    · simp only [more, decide_false, ite_false, Bool.false_eq_true]; rfl
  · intro σ pins
    unfold initMergeBlocks at pins
    split at pins <;> simp only [bf_init_mergeX61d4TSeg, bf_init_mergeX622cTSeg, bf_init_mergeX622cFSeg,
      List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, initmergehead_line_800061d4, initmergeempty_line_8000622c, initmergeempty_line_80006230, initmergeempty_line_80006234, initmergeempty_line_80006238, initmergeempty_line_8000623c, initmergeempty_line_80006240, initmergeempty_line_80006244, initmergeempty_line_80006248, initmergeempty_line_8000624c] at pins <;>
    rw [bit, next, succ] at pins <;>
    exact ⟨gholds_lookup (n := 16) _ pins rfl, gholds_lookup (n := 17) _ pins rfl, gholds_lookup (n := 6) _ pins rfl,
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 15) _ pins rfl,
      gholds_lookup (n := 30) _ pins rfl, gholds_lookup (n := 28) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · unfold initMergeBlocks; split <;> decide
end OCaml.Vm.Boot.Startup
