import OCaml.Vm.Boot.Startup.StrchrEntryNormalized
import OCaml.Vm.Boot.Startup.StrchrEntryImage
import OCaml.Vm.Boot.Startup.StrchrByteNormalized
import OCaml.Vm.Boot.Startup.StrchrByteImage
import OCaml.Vm.Boot.Startup.StrchrSetupNormalized
import OCaml.Vm.Boot.Startup.StrchrSetupImage
import OCaml.Vm.Boot.Startup.StrchrMasksNormalized
import OCaml.Vm.Boot.Startup.StrchrMasksImage
import OCaml.Vm.Boot.Startup.StrchrTestNormalized
import OCaml.Vm.Boot.Startup.StrchrTestImage
import OCaml.Vm.Boot.Startup.StrchrWordNormalized
import OCaml.Vm.Boot.Startup.StrchrWordImage
import OCaml.Vm.Boot.Startup.StrchrWordTestNormalized
import OCaml.Vm.Boot.Startup.StrchrWordTestImage
import OCaml.Vm.Boot.Startup.StrchrTailNormalized
import OCaml.Vm.Boot.Startup.StrchrTailImage
import OCaml.Vm.Boot.Startup.StrchrScanNormalized
import OCaml.Vm.Boot.Startup.StrchrScanImage
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! newlib's `strchr(s, '/')` (htif.c only searches for '/'): byte steps to
alignment, the word-at-a-time zero/slash test, then a byte scan. -/

theorem and7_toNat (a : BitVec 64) : (a &&& 7#64).toNat = a.toNat % 8 := by
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 3

def strchrEntryInput (a ra : BitVec 64) : GRegs := [(11, 47#64), (10, a), (1, ra)]

/-- A nonzero character; the start's alignment picks the byte or the word phase. -/
theorem strchr_entry (c : Config) (a ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrEntryInput a ra)) :
    FnSummary 0x80040704#64 (fun e => e = c)
      (WriteRegistersPost [13, 15] [] c (if a.toNat % 8 = 0 then 0x8004072c#64 else 0x80040714#64) a
        [(15, a &&& 7#64), (13, 47#64), (11, 47#64), (10, a), (1, ra)]) := by
  by_cases aligned : a.toNat % 8 = 0
  · have test : guardB bop.BEQ (a &&& 7#64) 0#64 = true := by
      simp only [guardB, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [and7_toNat, aligned]; rfl
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0704FSeg ++ strchrX0710TSeg) 0x80040704#64 (strchrEntryInput a ra) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [11, 10, 1]; decide
        shape := by change ChainOK _ [11, 10, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrEntry_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · change guardB bop.BEQ (47#64 &&& Functions.sign_extend (m := 64) 255#12) 0#64 = false
            decide
          · change guardB bop.BEQ (a &&& Functions.sign_extend (m := 64) 7#12) 0#64 = true
            rw [show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
            exact test }))
    · rfl
    · rw [if_pos aligned]; rfl
    · simp only [strchrX0704FSeg, strchrX0710TSeg, evalBlocks, evalBlock, SegEvalState.init, strchrentry_line_80040704, strchrentry_line_80040708, runGM, ldsRunM,
        wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrEntryInput, List.cons_append,
        List.nil_append]
      rw [show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide,
        show (47#64 &&& Functions.sign_extend (m := 64) 255#12) = 47#64 by decide]
    · rfl
    · decide
  · have test : guardB bop.BEQ (a &&& 7#64) 0#64 = false := by
      simp only [guardB, beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [and7_toNat] at this
      exact aligned this
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0704FSeg ++ strchrX0710FSeg) 0x80040704#64 (strchrEntryInput a ra) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [11, 10, 1]; decide
        shape := by change ChainOK _ [11, 10, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrEntry_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · change guardB bop.BEQ (47#64 &&& Functions.sign_extend (m := 64) 255#12) 0#64 = false
            decide
          · change guardB bop.BEQ (a &&& Functions.sign_extend (m := 64) 7#12) 0#64 = false
            rw [show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
            exact test }))
    · rfl
    · rw [if_neg aligned]; rfl
    · simp only [strchrX0704FSeg, strchrX0710FSeg, evalBlocks, evalBlock, SegEvalState.init, strchrentry_line_80040704, strchrentry_line_80040708, runGM, ldsRunM,
        wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrEntryInput, List.cons_append,
        List.nil_append]
      rw [show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide,
        show (47#64 &&& Functions.sign_extend (m := 64) 255#12) = 47#64 by decide]
    · rfl
    · decide

def strchrByteInput (p ra : BitVec 64) : GRegs := [(10, p), (13, 47#64), (11, 47#64), (1, ra)]

/-- A byte before alignment that is neither NUL nor '/'. -/
theorem strchr_byte_step (c : Config) (p ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrByteInput p ra)) (window : ReadWindow p 1)
    (pin : (c.σ.mem[p.toNat]?).getD 0 = b) (nz : b ≠ 0#8) (ns : b ≠ 47#8) :
    FnSummary 0x80040714#64 (fun e => e = c)
      (WriteRegistersPost [15, 10] [] c (if (p + 1#64).toNat % 8 = 0 then 0x8004072c#64 else 0x80040714#64) (p + 1#64)
        [(15, (p + 1#64) &&& 7#64), (10, p + 1#64), (13, 47#64), (11, 47#64), (1, ra)]) := by
  by_cases aligned : (p + 1#64).toNat % 8 = 0
  · have test : guardB bop.BNE ((p + 1#64) &&& 7#64) 0#64 = false := by
      simp only [guardB, bne_eq_false_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [and7_toNat, aligned]; rfl
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0714FSeg ++ strchrX071cFSeg ++ strchrX0720FSeg) 0x80040714#64
          (strchrByteInput p ra) [[b]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13, 11, 1]; decide
        shape := by change ChainOK _ [10, 13, 11, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrByte_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change p + Functions.sign_extend (m := 64) 0#12 = p
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · change guardB bop.BEQ (bytesVal .lbu [b]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of nz (by decide))
          · change guardB bop.BEQ (bytesVal .lbu [b]) 47#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of ns (by decide))
          · change guardB bop.BNE ((p + Functions.sign_extend (m := 64) 1#12) &&& Functions.sign_extend (m := 64) 7#12)
              0#64 = false
            rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
              show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
            exact test }))
    · rfl
    · rw [if_pos aligned]; rfl
    · simp only [strchrX0714FSeg, strchrX071cFSeg, strchrX0720FSeg, evalBlocks, evalBlock, SegEvalState.init, strchrbyte_line_80040714, strchrbyte_line_80040720, strchrbyte_line_80040724, runGM,
        ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrByteInput, List.cons_append,
        List.nil_append]
      rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
        show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
    · rfl
    · decide
  · have test : guardB bop.BNE ((p + 1#64) &&& 7#64) 0#64 = true := by
      simp only [guardB, bne_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [and7_toNat] at this
      exact aligned this
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0714FSeg ++ strchrX071cFSeg ++ strchrX0720TSeg) 0x80040714#64
          (strchrByteInput p ra) [[b]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13, 11, 1]; decide
        shape := by change ChainOK _ [10, 13, 11, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrByte_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change p + Functions.sign_extend (m := 64) 0#12 = p
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · change guardB bop.BEQ (bytesVal .lbu [b]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of nz (by decide))
          · change guardB bop.BEQ (bytesVal .lbu [b]) 47#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of ns (by decide))
          · change guardB bop.BNE ((p + Functions.sign_extend (m := 64) 1#12) &&& Functions.sign_extend (m := 64) 7#12)
              0#64 = true
            rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
              show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
            exact test }))
    · rfl
    · rw [if_neg aligned]; rfl
    · simp only [strchrX0714FSeg, strchrX071cFSeg, strchrX0720TSeg, evalBlocks, evalBlock, SegEvalState.init, strchrbyte_line_80040714, strchrbyte_line_80040720, strchrbyte_line_80040724, runGM,
        ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrByteInput, List.cons_append,
        List.nil_append]
      rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
        show Functions.sign_extend (m := 64) 7#12 = 7#64 by decide]
    · rfl
    · decide
/-- A NUL before alignment: no slash. -/
theorem strchr_byte_nul (c : Config) (p ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrByteInput p ra)) (window : ReadWindow p 1)
    (pin : (c.σ.mem[p.toNat]?).getD 0 = 0#8) :
    FnSummary 0x80040714#64 (fun e => e = c)
      (WriteRegistersPost [15] [] c 0x800407e0#64 p
        [(15, 0#64), (10, p), (13, 47#64), (11, 47#64), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput strchrX0714TSeg 0x80040714#64 (strchrByteInput p ra) [[0#8]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 13, 11, 1]; decide
      shape := by change ChainOK _ [10, 13, 11, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := strchrByte_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strchr_at_"
        · exact window.lbu rfl (by change p + Functions.sign_extend (m := 64) 0#12 = p
                                   rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
        · rfl }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- `return NULL`. -/
theorem strchr_none (c : Config) (ra a5 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(1, ra), (15, a5), (13, 47#64)]) :
    FnSummary 0x800407e0#64 (fun e => e = c)
      (WriteRegistersPost [10] [] c ra 0#64 [(10, 0#64), (1, ra), (15, a5), (13, 47#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput strchrX07e0Seg 0x800407e0#64 [(1, ra), (15, a5), (13, 47#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [1, 15, 13]; decide
      shape := by change ChainOK _ [1, 15, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := strchrTail_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strchr_at_"
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · exact ret_tgt ra leaf.aligned
  · change [(10, 0#64 + Functions.sign_extend (m := 64) 0#12), (1, ra), (15, a5), (13, 47#64)] = _
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · decide
def slashPattern : BitVec 64 := 0x2f2f2f2f2f2f2f2f#64
def lowOnes : BitVec 64 := 0xfefefefefefefeff#64
def highBits : BitVec 64 := 0x8080808080808080#64

def strchrWordInput (a ra : BitVec 64) : GRegs := [(11, 47#64), (10, a), (13, 47#64), (1, ra)]

/-- At alignment: start the byte pattern and load the first word. -/
theorem strchr_load (c : Config) (a ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrWordInput a ra)) (window : ReadWindow a 8) :
    FnSummary 0x8004072c#64 (fun e => e = c)
      (WriteRegistersPost [11, 17, 15, 14] [] c 0x80040744#64 a
        [(17, 0x2f2f2f2f#64), (14, bytesT c.σ.mem a.toNat 8), (15, 0x2f2f0000#64), (11, 47#64), (10, a),
          (13, 47#64), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput strchrX072cSeg 0x8004072c#64 (strchrWordInput a ra)
        [read8 c.σ.mem a.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 10, 13, 1]; decide
      shape := by change ChainOK _ [11, 10, 13, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := strchrSetup_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strchr_at_"
        exact window.ld rfl (by change a + Functions.sign_extend (m := 64) 0#12 = a
                                rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero])
          (read8_pins _ _) }))
  · rfl
  · rfl
  · simp only [strchrX072cSeg, evalBlocks, evalBlock, SegEvalState.init, strchrsetup_line_8004072c, strchrsetup_line_80040730, strchrsetup_line_80040734, strchrsetup_line_80040738, strchrsetup_line_8004073c, strchrsetup_line_80040740, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrWordInput, read8_value,
      List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by decide, by decide, by decide⟩
  · rfl
  · decide
def strchrLoaded (a ra x : BitVec 64) : GRegs :=
  [(17, 0x2f2f2f2f#64), (14, x), (15, 0x2f2f0000#64), (11, 47#64), (10, a), (13, 47#64), (1, ra)]

def strchrMasked (a ra x : BitVec 64) : GRegs :=
  [(12, 0x7f7f7f7f#64), (16, lowOnes), (15, slashPattern ^^^ x), (17, slashPattern), (11, 0xfffffffffefefeff#64),
    (14, x), (10, a), (13, 47#64), (1, ra)]

/-- Build the slash pattern and the carry masks. -/
theorem strchr_masks (c : Config) (a ra x : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrLoaded a ra x)) :
    FnSummary 0x80040744#64 (fun e => e = c)
      (WriteRegistersPost [11, 15, 16, 17, 12] [] c 0x80040768#64 a (strchrMasked a ra x)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput strchrX0744Seg 0x80040744#64 (strchrLoaded a ra x) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [17, 14, 15, 11, 10, 13, 1]; decide
      shape := by change ChainOK _ [17, 14, 15, 11, 10, 13, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := strchrMasks_code leaf.image
        chain_facts code with "Vsa.Sim.Code.strchr_at_" }))
  · rfl
  · rfl
  · simp only [strchrX0744Seg, evalBlocks, evalBlock, SegEvalState.init, strchrmasks_line_80040744, strchrmasks_line_80040748, strchrmasks_line_8004074c, strchrmasks_line_80040750, strchrmasks_line_80040754, strchrmasks_line_80040758, strchrmasks_line_8004075c, strchrmasks_line_80040760, strchrmasks_line_80040764, runGM, ldsRunM,
      wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrLoaded, strchrMasked,
      List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨by decide, by decide, ?_, by decide, by decide⟩
    congr 1
  · rfl
  · decide
def allOnes : BitVec 64 := 0xffffffffffffffff#64

/-- The first word's test: nonzero when the word may hold a NUL or a '/'. -/
def setupTest (x : BitVec 64) : BitVec 64 :=
  ((x + lowOnes) &&& (x ^^^ allOnes) ||| (slashPattern ^^^ x) + lowOnes &&& (slashPattern ^^^ x ^^^ allOnes)) &&&
    highBits

def strchrTested (a ra x : BitVec 64) : GRegs :=
  [(15, setupTest x), (6, highBits), (11, (slashPattern ^^^ x) + lowOnes &&& (slashPattern ^^^ x ^^^ allOnes)),
    (14, x ^^^ allOnes), (28, (slashPattern ^^^ x) + lowOnes), (12, 0x7f7f7f7f#64), (16, lowOnes),
    (17, slashPattern), (10, a), (13, 47#64), (1, ra)]

theorem guard_of_eq {op : bop} {v w r : BitVec 64} {b : Bool} (h : v = w) (g : guardB op w r = b) :
    guardB op v r = b := h ▸ g

local macro "test_regs" : tactic =>
  `(tactic| (
    rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨?_, by decide⟩
    unfold setupTest
    congr 1))

/-- The first word's test: a hit goes to the byte scan, a clear word to the loop. -/
theorem strchr_test (c : Config) (a ra x : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrMasked a ra x)) :
    FnSummary 0x80040768#64 (fun e => e = c)
      (WriteRegistersPost [28, 11, 6, 15, 14] [] c (if setupTest x = 0#64 then 0x80040798#64 else 0x800407d8#64) a
        (strchrTested a ra x)) := by
  by_cases clear : setupTest x = 0#64
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX0768FSeg 0x80040768#64 (strchrMasked a ra x) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [12, 16, 15, 17, 11, 14, 10, 13, 1]; decide
        shape := by change ChainOK _ [12, 16, 15, 17, 11, 14, 10, 13, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTest_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          refine guard_of_eq (w := setupTest x) ?_ (by rw [clear]; rfl)
          simp only [strchrtest_line_80040768, strchrtest_line_8004076c, strchrtest_line_80040770, strchrtest_line_80040774, strchrtest_line_80040778, strchrtest_line_8004077c, strchrtest_line_80040780, strchrtest_line_80040784, strchrtest_line_80040788, strchrtest_line_8004078c, strchrtest_line_80040790, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
            ite_true, ite_false, strchrMasked]
          rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide]
          unfold setupTest
          congr 1 }))
    · rfl
    · rw [if_pos clear]; rfl
    · simp only [strchrX0768FSeg, evalBlocks, evalBlock, SegEvalState.init, strchrtest_line_80040768, strchrtest_line_8004076c, strchrtest_line_80040770, strchrtest_line_80040774, strchrtest_line_80040778, strchrtest_line_8004077c, strchrtest_line_80040780, strchrtest_line_80040784, strchrtest_line_80040788, strchrtest_line_8004078c, strchrtest_line_80040790, runGM, ldsRunM,
        wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrMasked, strchrTested]
      test_regs
    · rfl
    · decide
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX0768TSeg 0x80040768#64 (strchrMasked a ra x) [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [12, 16, 15, 17, 11, 14, 10, 13, 1]; decide
        shape := by change ChainOK _ [12, 16, 15, 17, 11, 14, 10, 13, 1] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTest_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          refine guard_of_eq (w := setupTest x) ?_ (by simp only [guardB, bne_iff_ne]; exact clear)
          simp only [strchrtest_line_80040768, strchrtest_line_8004076c, strchrtest_line_80040770, strchrtest_line_80040774, strchrtest_line_80040778, strchrtest_line_8004077c, strchrtest_line_80040780, strchrtest_line_80040784, strchrtest_line_80040788, strchrtest_line_8004078c, strchrtest_line_80040790, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff,
            ite_true, ite_false, strchrMasked]
          rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide]
          unfold setupTest
          congr 1 }))
    · rfl
    · rw [if_neg clear]; rfl
    · simp only [strchrX0768TSeg, evalBlocks, evalBlock, SegEvalState.init, strchrtest_line_80040768, strchrtest_line_8004076c, strchrtest_line_80040770, strchrtest_line_80040774, strchrtest_line_80040778, strchrtest_line_8004077c, strchrtest_line_80040780, strchrtest_line_80040784, strchrtest_line_80040788, strchrtest_line_8004078c, strchrtest_line_80040790, runGM, ldsRunM,
        wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrMasked, strchrTested]
      test_regs
    · rfl
    · decide
/-- A later word's test (the loop's operand order). -/
def loopTest (x : BitVec 64) : BitVec 64 :=
  ((x + lowOnes) &&& (x ^^^ allOnes) ||| (x ^^^ slashPattern ^^^ allOnes) &&& ((x ^^^ slashPattern) + lowOnes)) &&&
    highBits

def strchrLoopInput (w : BitVec 64) : GRegs := [(10, w), (17, slashPattern), (16, lowOnes), (6, highBits)]

def strchrLooped (w x : BitVec 64) : GRegs :=
  [(15, loopTest x), (12, (x ^^^ slashPattern ^^^ allOnes) &&& (x ^^^ slashPattern) + lowOnes), (14, x ^^^ allOnes),
    (11, x ^^^ slashPattern ^^^ allOnes), (10, w + 8#64), (17, slashPattern), (16, lowOnes), (6, highBits)]

/-- The next word: a clear word stays in the loop, a hit goes to the byte scan. -/
theorem strchr_word_step (c : Config) (w ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strchrLoopInput w)) (window : ReadWindow (w + 8#64) 8) :
    FnSummary 0x80040798#64 (fun e => e = c)
      (WriteRegistersPost [14, 10, 15, 11, 12] [] c
        (if loopTest (bytesT c.σ.mem (w + 8#64).toNat 8) = 0#64 then 0x80040798#64 else 0x800407c8#64) (w + 8#64)
        (strchrLooped w (bytesT c.σ.mem (w + 8#64).toNat 8))) := by
  by_cases clear : loopTest (bytesT c.σ.mem (w + 8#64).toNat 8) = 0#64
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0798Seg ++ strchrX07a8TSeg) 0x80040798#64 (strchrLoopInput w)
          [read8 c.σ.mem (w + 8#64).toNat] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 17, 16, 6]; decide
        shape := by change ChainOK _ [10, 17, 16, 6] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrWord_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.ld rfl (by change w + Functions.sign_extend (m := 64) 8#12 = w + 8#64
                                    rw [show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]) (read8_pins _ _)
          · refine guard_of_eq (w := loopTest (bytesT c.σ.mem (w + 8#64).toNat 8)) ?_ (by rw [clear]; rfl)
            simp only [strchrword_line_80040798, strchrword_line_8004079c, strchrword_line_800407a0, strchrword_line_800407a4, strchrwordtest_line_800407a8, strchrwordtest_line_800407ac, strchrwordtest_line_800407b0, strchrwordtest_line_800407b4, strchrwordtest_line_800407b8, strchrwordtest_line_800407bc, strchrwordtest_line_800407c0, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
              wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true,
              ite_false, strchrLoopInput, read8_value]
            rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide]
            rfl }))
    · rfl
    · rw [if_pos clear]; rfl
    · simp only [strchrX0798Seg, strchrX07a8TSeg, evalBlocks, evalBlock, SegEvalState.init, strchrword_line_80040798, strchrword_line_8004079c, strchrword_line_800407a0, strchrword_line_800407a4, strchrwordtest_line_800407a8, strchrwordtest_line_800407ac, strchrwordtest_line_800407b0, strchrwordtest_line_800407b4, strchrwordtest_line_800407b8, strchrwordtest_line_800407bc, strchrwordtest_line_800407c0, runGM,
        ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrLoopInput, List.cons_append,
        List.nil_append, read8_value, strchrLooped]
      rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide,
        show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
      rfl
    · rfl
    · decide
  · apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX0798Seg ++ strchrX07a8FSeg) 0x80040798#64 (strchrLoopInput w)
          [read8 c.σ.mem (w + 8#64).toNat] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 17, 16, 6]; decide
        shape := by change ChainOK _ [10, 17, 16, 6] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrWord_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.ld rfl (by change w + Functions.sign_extend (m := 64) 8#12 = w + 8#64
                                    rw [show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]) (read8_pins _ _)
          · refine guard_of_eq (w := loopTest (bytesT c.σ.mem (w + 8#64).toNat 8)) ?_ (by simp only [guardB, beq_eq_false_iff_ne]; exact clear)
            simp only [strchrword_line_80040798, strchrword_line_8004079c, strchrword_line_800407a0, strchrword_line_800407a4, strchrwordtest_line_800407a8, strchrwordtest_line_800407ac, strchrwordtest_line_800407b0, strchrwordtest_line_800407b4, strchrwordtest_line_800407b8, strchrwordtest_line_800407bc, strchrwordtest_line_800407c0, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
              wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true,
              ite_false, strchrLoopInput, read8_value]
            rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide]
            rfl }))
    · rfl
    · rw [if_neg clear]; rfl
    · simp only [strchrX0798Seg, strchrX07a8FSeg, evalBlocks, evalBlock, SegEvalState.init, strchrword_line_80040798, strchrword_line_8004079c, strchrword_line_800407a0, strchrword_line_800407a4, strchrwordtest_line_800407a8, strchrwordtest_line_800407ac, strchrwordtest_line_800407b0, strchrwordtest_line_800407b4, strchrwordtest_line_800407b8, strchrwordtest_line_800407bc, strchrwordtest_line_800407c0, runGM,
        ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
        List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, strchrLoopInput, List.cons_append,
        List.nil_append, read8_value, strchrLooped]
      rw [show Functions.sign_extend (m := 64) 4095#12 = allOnes by decide,
        show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
      rfl
    · rfl
    · decide
/-- Byte scan, first load (after a first-word hit). -/
theorem strchr_scan_first (c : Config) (q ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (13, 47#64)]) (window : ReadWindow q 1) (pin : (c.σ.mem[q.toNat]?).getD 0 = b) :
    FnSummary 0x800407d8#64 (fun e => e = c)
      (WriteRegistersPost [15] [] c (if b = 0#8 then 0x800407e0#64 else 0x800407d0#64) q
        [(15, nameByteWord b), (10, q), (13, 47#64)]) := by
  by_cases zero : b = 0#8
  · subst zero
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX07d8FSeg 0x800407d8#64 [(10, q), (13, 47#64)] [[0#8]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13]; decide
        shape := by change ChainOK _ [10, 13] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrScan_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change q + Functions.sign_extend (m := 64) 0#12 = q
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · rfl }))
    · rfl
    · rw [if_pos rfl]; rfl
    · change [(15, bytesVal .lbu [0#8]), (10, q), (13, 47#64)] = _
      rw [name_lbu_value]
    · rfl
    · decide
  · have nz : nameByteWord b ≠ 0#64 := nameByteWord_ne_of zero (by decide)
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX07d8TSeg 0x800407d8#64 [(10, q), (13, 47#64)] [[b]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13]; decide
        shape := by change ChainOK _ [10, 13] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrScan_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change q + Functions.sign_extend (m := 64) 0#12 = q
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · change guardB bop.BNE (bytesVal .lbu [b]) 0#64 = true
            rw [name_lbu_value]
            exact bne_iff_ne.mpr nz }))
    · rfl
    · rw [if_neg zero]; rfl
    · change [(15, bytesVal .lbu [b]), (10, q), (13, 47#64)] = _
      rw [name_lbu_value]
    · rfl
    · decide
/-- Byte scan, first load (after a later word's hit). -/
theorem strchr_scan_word (c : Config) (q ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (13, 47#64)]) (window : ReadWindow q 1) (pin : (c.σ.mem[q.toNat]?).getD 0 = b) :
    FnSummary 0x800407c8#64 (fun e => e = c)
      (WriteRegistersPost [15] [] c (if b = 0#8 then 0x800407e0#64 else 0x800407d0#64) q
        [(15, nameByteWord b), (10, q), (13, 47#64)]) := by
  by_cases zero : b = 0#8
  · subst zero
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX07c8TSeg 0x800407c8#64 [(10, q), (13, 47#64)] [[0#8]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13]; decide
        shape := by change ChainOK _ [10, 13] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTail_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change q + Functions.sign_extend (m := 64) 0#12 = q
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · rfl }))
    · rfl
    · rw [if_pos rfl]; rfl
    · change [(15, bytesVal .lbu [0#8]), (10, q), (13, 47#64)] = _
      rw [name_lbu_value]
    · rfl
    · decide
  · have nz : nameByteWord b ≠ 0#64 := nameByteWord_ne_of zero (by decide)
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput strchrX07c8FSeg 0x800407c8#64 [(10, q), (13, 47#64)] [[b]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13]; decide
        shape := by change ChainOK _ [10, 13] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTail_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact window.lbu rfl (by change q + Functions.sign_extend (m := 64) 0#12 = q
                                     rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) pin
          · change guardB bop.BEQ (bytesVal .lbu [b]) 0#64 = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr nz }))
    · rfl
    · rw [if_neg zero]; rfl
    · change [(15, bytesVal .lbu [b]), (10, q), (13, 47#64)] = _
      rw [name_lbu_value]
    · rfl
    · decide

/-- One scan step: the current byte is not '/'; load the next. -/
theorem strchr_scan_step (c : Config) (q ra : BitVec 64) (b next : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, q), (13, 47#64), (15, nameByteWord b)]) (notSlash : b ≠ 47#8)
    (window : ReadWindow (q + 1#64) 1) (pin : (c.σ.mem[(q + 1#64).toNat]?).getD 0 = next) :
    FnSummary 0x800407d0#64 (fun e => e = c)
      (WriteRegistersPost [10, 15] [] c (if next = 0#8 then 0x800407e0#64 else 0x800407d0#64) (q + 1#64)
        [(15, nameByteWord next), (10, q + 1#64), (13, 47#64)]) := by
  have ne : guardB bop.BEQ 47#64 (nameByteWord b) = false := by
    simp only [guardB, beq_eq_false_iff_ne]
    exact fun h => nameByteWord_ne_of notSlash (by decide) h.symm
  have addr : q + Functions.sign_extend (m := 64) 1#12 + Functions.sign_extend (m := 64) 0#12 = q + 1#64 := by
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
  by_cases zero : next = 0#8
  · subst zero
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX07d0FSeg ++ strchrX07d4FSeg) 0x800407d0#64
          [(10, q), (13, 47#64), (15, nameByteWord b)] [[0#8]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13, 15]; decide
        shape := by change ChainOK _ [10, 13, 15] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTail_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact ne
          · exact window.lbu rfl addr pin
          · rfl }))
    · rfl
    · rw [if_pos rfl]; rfl
    · change [(15, bytesVal .lbu [0#8]), (10, q + Functions.sign_extend (m := 64) 1#12), (13, 47#64)] = _
      rw [name_lbu_value, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
    · rfl
    · decide
  · have nz : nameByteWord next ≠ 0#64 := nameByteWord_ne_of zero (by decide)
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (strchrX07d0FSeg ++ strchrX07d4TSeg) 0x800407d0#64
          [(10, q), (13, 47#64), (15, nameByteWord b)] [[next]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 13, 15]; decide
        shape := by change ChainOK _ [10, 13, 15] _; decide
        tick := leaf.tick
        facts := by
          have code := strchrTail_code leaf.image
          chain_facts code with "Vsa.Sim.Code.strchr_at_"
          · exact ne
          · exact window.lbu rfl addr pin
          · change guardB bop.BNE (bytesVal .lbu [next]) 0#64 = true
            rw [name_lbu_value]
            exact bne_iff_ne.mpr nz }))
    · rfl
    · rw [if_neg zero]; rfl
    · change [(15, bytesVal .lbu [next]), (10, q + Functions.sign_extend (m := 64) 1#12), (13, 47#64)] = _
      rw [name_lbu_value, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
    · rfl
    · decide
end OCaml.Vm.Boot.Startup
