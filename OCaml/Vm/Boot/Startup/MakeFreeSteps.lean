import OCaml.Vm.Boot.Startup.MfbEntryNormalized
import OCaml.Vm.Boot.Startup.MfbEntryImage
import OCaml.Vm.Boot.Startup.MfbFrameNormalized
import OCaml.Vm.Boot.Startup.MfbFrameImage
import OCaml.Vm.Boot.Startup.MfbSaveNormalized
import OCaml.Vm.Boot.Startup.MfbSaveImage
import OCaml.Vm.Boot.Startup.MfbSetupNormalized
import OCaml.Vm.Boot.Startup.MfbSetupImage
import OCaml.Vm.Boot.Startup.MfbLoopNormalized
import OCaml.Vm.Boot.Startup.MfbLoopImage
import OCaml.Vm.Boot.Startup.MfbMergeNormalized
import OCaml.Vm.Boot.Startup.MfbMergeImage
import OCaml.Vm.Boot.Startup.MfbInsertCallNormalized
import OCaml.Vm.Boot.Startup.MfbInsertCallImage
import OCaml.Vm.Boot.Startup.MfbCountNormalized
import OCaml.Vm.Boot.Startup.MfbCountImage
import OCaml.Vm.Boot.Startup.MfbNextNormalized
import OCaml.Vm.Boot.Startup.MfbNextImage
import OCaml.Vm.Boot.Startup.MfbReturnNormalized
import OCaml.Vm.Boot.Startup.MfbReturnImage
import OCaml.Vm.Boot.Startup.MfbInsertCallCallInterface
import OCaml.Vm.Boot.Startup.InsertBlock
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! bf_make_free_blocks(p, size, merge, color)'s blocks on a chunk smaller than
`Max_wosize` words with merging on: one free block, inserted into the tree. -/

/-- A nonempty chunk; open an 80-byte frame. -/
theorem mfb_entry (c : Config) (sp ra p size : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, size), (2, sp), (10, p)]) (nonempty : size ≠ 0#64) :
    FnSummary 0x80006fac#64 (fun e => e = c) (WriteRegistersPost [2] [] c 0x80006fb4#64 p
      [(11, size), (2, nativeStack sp 80), (10, p)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (bf_make_free_blocksX6facFSeg ++ bf_make_free_blocksX6fb0Seg) 0x80006fac#64
        [(11, size), (2, sp), (10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 2, 10]; decide
      shape := by change ChainOK _ [11, 2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbEntry_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · change guardB bop.BEQ size 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonempty }))
  · rfl
  · rfl
  · intro σ pins
    exact ⟨gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · decide

def mfbSlots (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : BitVec 64) : List (Nat × BitVec 64) :=
  [(8, s7), (48, s2), (40, s3), (32, s4), (24, s5), (16, s6), (0, s8), (72, ra), (64, s0), (56, s1)]

/-- Save s7, s2–s6, s8, ra, s0, s1; `s7 = 1`. -/
theorem mfb_save (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 p : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80)
    (regs : GHolds c.σ [(23, s7), (2, nativeStack sp 80), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (24, s8),
      (1, ra), (8, s0), (9, s1), (10, p)]) :
    FnSummary 0x80006fb4#64 (fun e => e = c) (WriteRegistersPost [23]
      (nativeWordLog sp 80 (mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8)) c 0x80006fe0#64 p
      [(23, 1#64), (2, nativeStack sp 80), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (24, s8), (1, ra),
        (8, s0), (9, s1), (10, p)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (nativeWordLog sp 80 (mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8)) :=
    frame.word_log_inside fun off value member => by simp [mfbSlots] at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput bf_make_free_blocksX6fb4Seg 0x80006fb4#64
        [(23, s7), (2, nativeStack sp 80), (18, s2), (19, s3), (20, s4), (21, s5), (22, s6), (24, s8), (1, ra), (8, s0),
          (9, s1), (10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [23, 2, 18, 19, 20, 21, 22, 24, 1, 8, 9, 10]; decide
      shape := by change ChainOK _ [23, 2, 18, 19, 20, 21, 22, 24, 1, 8, 9, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [bf_make_free_blocksX6fb4Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, mfbsave_line_80006fb4, mfbsave_line_80006fb8, mfbsave_line_80006fbc, mfbsave_line_80006fc0, mfbsave_line_80006fc4, mfbsave_line_80006fc8, mfbsave_line_80006fcc, mfbsave_line_80006fd0, mfbsave_line_80006fd4, mfbsave_line_80006fd8, mfbsave_line_80006fdc] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 2) _ pins rfl, gholds_lookup (n := 18) _ pins rfl,
      gholds_lookup (n := 19) _ pins rfl, gholds_lookup (n := 20) _ pins rfl, gholds_lookup (n := 21) _ pins rfl,
      gholds_lookup (n := 22) _ pins rfl, gholds_lookup (n := 24) _ pins rfl, gholds_lookup (n := 1) _ pins rfl,
      gholds_lookup (n := 8) _ pins rfl, gholds_lookup (n := 9) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_fl_cur_wsz`. -/
def flCurWszAddr : Nat := 0x80064a40

/-- Keep the arguments; `s7 = Max_wosize + 1`, `s4 = BF_NUM_SMALL`, `s5 = &caml_fl_cur_wsz`. -/
theorem mfb_setup (c : Config) (ra p size merge color : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, size), (10, p), (13, color), (12, merge), (23, 1#64)]) :
    FnSummary 0x80006fe0#64 (fun e => e = c) (WriteRegistersPost [18, 19, 22, 24, 23, 20, 21] [] c 0x80007030#64 p
      [(18, size), (19, p), (22, color), (24, merge), (23, 1#64 <<< 54), (20, 16#64), (21, 0x80064a40#64),
        (11, size), (10, p), (13, color), (12, merge)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput bf_make_free_blocksX6fe0Seg 0x80006fe0#64
        [(11, size), (10, p), (13, color), (12, merge), (23, 1#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 10, 13, 12, 23]; decide
      shape := by change ChainOK _ [11, 10, 13, 12, 23] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbSetup_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_" }))
  · rfl
  · rfl
  · intro σ pins
    simp only [bf_make_free_blocksX6fe0Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, mfbsetup_line_80006fe0, mfbsetup_line_80006fe4, mfbsetup_line_80006fe8, mfbsetup_line_80006fec, mfbsetup_line_80006ff0, mfbsetup_line_80006ff4, mfbsetup_line_80006ff8, mfbsetup_line_80006ffc] at pins
    simp only [sext_zero, BitVec.add_zero] at pins
    exact ⟨gholds_lookup (n := 18) _ pins rfl, gholds_lookup (n := 19) _ pins rfl, gholds_lookup (n := 22) _ pins rfl,
      gholds_lookup (n := 24) _ pins rfl, gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 10) _ pins rfl,
      gholds_lookup (n := 13) _ pins rfl, gholds_lookup (n := 12) _ pins rfl, trivial⟩
  · rfl
  · decide

theorem sltiu_ge (w : BitVec 64) (h : 17 ≤ w.toNat) :
    compareValue true w (Functions.sign_extend (m := 64) 17#12) = 0#64 := by
  unfold compareValue
  rw [show Functions.sign_extend (m := 64) 17#12 = 17#64 by decide]
  have lt : Functions.zopz0zI_u w 17#64 = false := by
    unfold Functions.zopz0zI_u
    simp only [Sail.BitVec.toNatInt, decide_eq_false_iff_not, Int.ofNat_eq_natCast, Int.ofNat_lt, BitVec.toNat_ofNat]
    omega
  simp only [ite_true, lt]
  decide

theorem slli_ten (x : BitVec 64) (a : MInstr) (imm : a.imm = 10#12) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb (shamtOf a) 5 0) = x <<< 10 := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq']
  rfl

theorem pred_size (size : BitVec 64) :
    size + Functions.sign_extend (m := 64) 0#12 + Functions.sign_extend (m := 64) 4095#12 = size - 1#64 := by
  rw [sext_zero, BitVec.add_zero, show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide,
    ← BitVec.sub_eq_add_neg]

theorem slliw_blue (a : MInstr) (sh : shamt5Of a = 9#5) :
    Functions.sign_extend (m := 64) (Sail.shift_bits_left (Sail.BitVec.extractLsb
      (compareValue true 0#64 (Functions.sign_extend (m := 64) 1#12)) 31 0) (shamt5Of a)) = 512#64 := by
  rw [sh]
  decide

/-- A blue block header with wosize `size - 1`. -/
def mfbHeader (size : BitVec 64) : BitVec 64 := 512#64 + ((size - 1#64) <<< 10)

theorem header_wosize (size : BitVec 64) (fits : size.toNat ≤ 2 ^ 54) (large : 18 ≤ size.toNat) :
    mfbHeader size >>> 10 = size - 1#64 := by
  apply BitVec.eq_of_toNat_eq
  unfold mfbHeader
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow]
  have b := size.isLt
  simp only [Nat.reducePow] at fits b
  omega

local macro "mlk" : tactic => `(tactic| simp only [mfbloop_line_80007030, mfbloop_line_80007038, mfbloop_line_8000703c, mfbloop_line_80007040, mfbloop_line_80007044, mfbloop_line_80007048, mfbloop_line_8000704c, mfbmerge_line_80007004, mfbmerge_line_80007008, mfbmerge_line_8000700c, mfbmerge_line_80007010, mfbmerge_line_80007014, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff])

/-- One whole-chunk block, blue, merged into the tree. -/
theorem mfb_block (c : Config) (ra p size color merge : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(18, size), (23, 1#64 <<< 54), (22, color), (24, merge), (19, p), (20, 16#64), (10, p)])
    (fits : size.toNat ≤ 2 ^ 54) (large : 18 ≤ size.toNat) (merging : merge ≠ 0#64) (window : WriteWindow p 8)
    (outside : ImageOutside [(p.toNat, 8, mfbHeader size)]) :
    FnSummary 0x80007030#64 (fun e => e = c) (WriteRegistersPost [9, 15, 14, 13, 22, 8, 10]
      [(p.toNat, 8, mfbHeader size)] c 0x80007098#64 (p + 8#64)
      [(9, size), (15, mfbHeader size), (14, 1#64), (13, color + (size - 1#64) <<< 10), (22, 512#64), (8, size - 1#64),
        (10, p + 8#64), (18, size), (23, 1#64 <<< 54), (24, merge), (19, p), (20, 16#64)]) := by
  have pred : 17 ≤ (size - 1#64).toNat := by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput (bf_make_free_blocksX7030TSeg ++ bf_make_free_blocksX703cTSeg ++
        bf_make_free_blocksX7004TSeg) 0x80007030#64
        [(18, size), (23, 1#64 <<< 54), (22, color), (24, merge), (19, p), (20, 16#64), (10, p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 23, 22, 24, 19, 20, 10]; decide
      shape := by change ChainOK _ [18, 23, 22, 24, 19, 20, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbLoop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · mlk
          unfold guardB Functions.zopz0zKzJ_u
          simp only [Sail.BitVec.toNatInt]
          apply decide_eq_true
          apply Int.ofNat_le.mpr
          simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
          omega
        · mlk
          unfold guardB
          simp only [bne, merging, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, not_false_eq_true]
        · exact window.sd rfl (by mlk; rw [sext_zero, BitVec.add_zero])
        · mlk
          rw [pred_size, sltiu_ge _ (by rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega),
            slli_ten _ _ rfl, srli_ten _ _ rfl]
          rw [slliw_blue _ rfl]
          rw [show 512#64 + (size - 1#64) <<< 10 = mfbHeader size from rfl, header_wosize size fits large]
          unfold guardB Functions.zopz0zI_u
          simp only [Sail.BitVec.toNatInt]
          apply decide_eq_true
          apply Int.ofNat_lt.mpr
          rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega }))
  · simp only [bf_make_free_blocksX7030TSeg, bf_make_free_blocksX703cTSeg, bf_make_free_blocksX7004TSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      wlogM, wentryM, widthOfM, eaddrM, mfbloop_line_80007030, mfbloop_line_80007038, mfbloop_line_8000703c, mfbloop_line_80007040, mfbloop_line_80007044, mfbloop_line_80007048, mfbloop_line_8000704c, mfbmerge_line_80007004, mfbmerge_line_80007008, mfbmerge_line_8000700c, mfbmerge_line_80007010, mfbmerge_line_80007014]
    rw [pred_size, sltiu_ge _ pred, slli_ten _ _ rfl, slliw_blue _ rfl, sext_zero, BitVec.add_zero]
    rfl
  · rfl
  · intro σ pins
    simp only [bf_make_free_blocksX7030TSeg, bf_make_free_blocksX703cTSeg, bf_make_free_blocksX7004TSeg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      mfbloop_line_80007030, mfbloop_line_80007038, mfbloop_line_8000703c, mfbloop_line_80007040, mfbloop_line_80007044, mfbloop_line_80007048, mfbloop_line_8000704c, mfbmerge_line_80007004, mfbmerge_line_80007008, mfbmerge_line_8000700c, mfbmerge_line_80007010, mfbmerge_line_80007014] at pins
    rw [pred_size, sltiu_ge _ pred, slli_ten _ _ rfl, slliw_blue _ rfl, show 512#64 + (size - 1#64) <<< 10 = mfbHeader size
      from rfl, srli_ten _ _ rfl, header_wosize size fits large] at pins
    exact ⟨gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]), gholds_lookup (n := 15) _ pins rfl,
      gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 13) _ pins rfl, gholds_lookup (n := 22) _ pins rfl,
      gholds_lookup (n := 8) _ pins rfl, gholds_lookup_eq pins rfl (by rw [show Functions.sign_extend (m := 64) 8#12 = 8#64
        by decide]), gholds_lookup (n := 18) _ pins rfl, gholds_lookup (n := 23) _ pins rfl,
      gholds_lookup (n := 24) _ pins rfl, gholds_lookup (n := 19) _ pins rfl, gholds_lookup (n := 20) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- `caml_fl_cur_wsz += Whsize_wosize(wosize)`. -/
theorem mfb_count (c : Config) (ra wos cur v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(21, 0x80064a40#64), (8, wos), (10, v)]) (curWord : bytesT c.σ.mem flCurWszAddr 8 = cur) :
    FnSummary 0x8000709c#64 (fun e => e = c) (WriteRegistersPost [15] [(flCurWszAddr, 8, cur + 1#64 + wos)] c
      0x80007020#64 v [(15, cur + 1#64 + wos), (21, 0x80064a40#64), (8, wos), (10, v)]) := by
  have word : bytesVal .ld (read8 c.σ.mem (0x80064a40#64).toNat) = cur := by rw [read8_value]; exact curWord
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, flCurWszAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput bf_make_free_blocksX709cSeg 0x8000709c#64
        [(21, 0x80064a40#64), (8, wos), (10, v)] [read8 c.σ.mem (0x80064a40#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [21, 8, 10]; decide
      shape := by change ChainOK _ [21, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbCount_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · exact (show ReadWindow (0x80064a40#64) 8 by constructor <;> decide).ld rfl
            (by simp only [mfbcount_line_8000709c, mfbcount_line_800070a0, mfbcount_line_800070a4, mfbcount_line_800070a8, eaddrM, srcVal, lookupG, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
            (read8_pins _ _)
        · exact (show WriteWindow (BitVec.ofNat 64 flCurWszAddr) 8 by constructor <;> decide).sd rfl
            (by simp only [mfbcount_line_8000709c, mfbcount_line_800070a0, mfbcount_line_800070a4, mfbcount_line_800070a8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
              Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons]; decide) }))
  · simp only [bf_make_free_blocksX709cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, mfbcount_line_8000709c, mfbcount_line_800070a0, mfbcount_line_800070a4, mfbcount_line_800070a8]
    rw [word, sext_zero, BitVec.add_zero, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
    rfl
  · rfl
  · intro σ pins
    simp only [bf_make_free_blocksX709cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM,
      srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.headD_cons,
      List.tail_cons, mfbcount_line_8000709c, mfbcount_line_800070a0, mfbcount_line_800070a4, mfbcount_line_800070a8] at pins
    rw [word, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide] at pins
    exact ⟨gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 21) _ pins rfl, gholds_lookup (n := 8) _ pins rfl,
      gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- The chunk is used up. -/
theorem mfb_next (c : Config) (ra size p v : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(18, size), (9, size), (19, p), (10, v)]) :
    FnSummary 0x80007020#64 (fun e => e = c) (WriteRegistersPost [18, 9, 19] [] c 0x80007068#64 v
      [(18, 0#64), (9, size <<< 3), (19, p + size <<< 3), (10, v)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput bf_make_free_blocksX7020TSeg 0x80007020#64
        [(18, size), (9, size), (19, p), (10, v)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 9, 19, 10]; decide
      shape := by change ChainOK _ [18, 9, 19, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbNext_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · simp only [mfbnext_line_80007020, mfbnext_line_80007024, mfbnext_line_80007028, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false,
            Nat.reduceEqDiff, BitVec.sub_self]
          rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [bf_make_free_blocksX7020TSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, BitVec.sub_self, mfbnext_line_80007020, mfbnext_line_80007024, mfbnext_line_80007028] at pins
    exact ⟨gholds_lookup (n := 18) _ pins rfl, gholds_lookup_eq pins rfl (slli_three _ _ rfl),
      gholds_lookup_eq pins rfl (by rw [slli_three _ _ rfl]), gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

def mfbSavedLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [Primitives.read8 m (nativeFrameBase sp 80 + 72), Primitives.read8 m (nativeFrameBase sp 80 + 64), Primitives.read8 m (nativeFrameBase sp 80 + 56), Primitives.read8 m (nativeFrameBase sp 80 + 48), Primitives.read8 m (nativeFrameBase sp 80 + 40), Primitives.read8 m (nativeFrameBase sp 80 + 32), Primitives.read8 m (nativeFrameBase sp 80 + 24), Primitives.read8 m (nativeFrameBase sp 80 + 16), Primitives.read8 m (nativeFrameBase sp 80 + 8), Primitives.read8 m (nativeFrameBase sp 80 + 0)]

/-- Restore ra, s0–s8 and return. -/
theorem mfb_return (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ [(2, nativeStack sp 80), (10, v)])
    (saved : ∀ off value, (off, value) ∈ mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8 →
      bytesT c.σ.mem (nativeFrameBase sp 80 + off) 8 = value)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80007068#64 (fun e => e = c) (WriteRegistersPost [1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 2] [] c ra v
      [(2, sp), (24, s8), (23, s7), (22, s6), (21, s5), (20, s4), (19, s3), (18, s2), (9, s1), (8, s0), (1, ra),
        (10, v)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ mfbSlots ra s0 s1 s2 s3 s4 s5 s6 s7 s8) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput bf_make_free_blocksX7068Seg 0x80007068#64
        [(2, nativeStack sp 80), (10, v)] (mfbSavedLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := mfbReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_make_free_blocks_at_"
        · exact (frame.read_slot (off := 72) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 64) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 72 ra (by simp [mfbSlots]), ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word 72 ra (by simp [mfbSlots]), ret_tgt ra aligned]
  · simp only [bf_make_free_blocksX7068Seg, mfbSavedLoads, evalBlocks, evalBlock, SegEvalState.init, runGM,
      stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, mfbreturn_line_80007068, mfbreturn_line_8000706c, mfbreturn_line_80007070, mfbreturn_line_80007074, mfbreturn_line_80007078, mfbreturn_line_8000707c, mfbreturn_line_80007080, mfbreturn_line_80007084, mfbreturn_line_80007088, mfbreturn_line_8000708c, mfbreturn_line_80007090]
    rw [show Functions.sign_extend (m := 64) 80#12 = 80#64 by decide, nativeStack_restore, word 72 ra (by simp [mfbSlots]), word 64 s0 (by simp [mfbSlots]), word 56 s1 (by simp [mfbSlots]), word 48 s2 (by simp [mfbSlots]), word 40 s3 (by simp [mfbSlots]), word 32 s4 (by simp [mfbSlots]), word 24 s5 (by simp [mfbSlots]), word 16 s6 (by simp [mfbSlots]), word 8 s7 (by simp [mfbSlots]), word 0 s8 (by simp [mfbSlots])]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
