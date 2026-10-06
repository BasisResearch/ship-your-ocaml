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
end OCaml.Vm.Boot.Startup
