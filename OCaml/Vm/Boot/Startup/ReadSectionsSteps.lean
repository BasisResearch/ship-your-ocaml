import OCaml.Vm.Boot.Startup.AttemptOk
import OCaml.Vm.Boot.Startup.CamlAttemptRetryTestNormalized
import OCaml.Vm.Boot.Startup.CamlAttemptRetryTestImage
import OCaml.Vm.Boot.Startup.CamlReadSectionsNormalized
import OCaml.Vm.Boot.Startup.CamlReadSectionsImage
import OCaml.Vm.Boot.Startup.CamlReadSectionsCallInterface
import OCaml.Vm.Boot.Startup.ReadSectionsEntryNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsEntryImage
import OCaml.Vm.Boot.Startup.ReadSectionsNumNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsNumImage
import OCaml.Vm.Boot.Startup.ReadSectionsNumCallInterface
import OCaml.Vm.Boot.Startup.ReadSectionsSeekNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsSeekImage
import OCaml.Vm.Boot.Startup.ReadSectionsReadNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsReadImage
import OCaml.Vm.Boot.Startup.ReadSectionsTestNormalized
import OCaml.Vm.Boot.Startup.ReadSectionsTestImage
import OCaml.Vm.Boot.Startup.ReadSectionsSeekCallInterface
import OCaml.Vm.Boot.Startup.ReadSectionsReadCallInterface
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_main after caml_attempt_open returned a descriptor: on to
`caml_read_section_descriptors(fd, &trail)`. -/

local macro "rsk" : tactic => `(tactic| simp only [camlattemptretrytest_line_80005130, camlattemptretrytest_line_80005134, camlattemptretrytest_line_8000513c, camlattemptretrytest_line_80005140, camlattemptretrytest_line_80005148, camlreadsections_line_80004e08, camlreadsections_line_80004e0c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The descriptor is neither -2, -1 nor -3: read the section table. -/
theorem caml_read_sections_front (c : Config) (ra fd : BitVec 64) (w : List (BitVec 8)) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (2, parameterStack)])
    (saved : read8 c.σ.mem (parameterStack.toNat + 24) = w)
    (notTwo : fd ≠ -2#64) (notOne : fd ≠ -1#64) (notThree : fd ≠ -3#64) :
    FnSummary 0x80005130#64 (fun d => d = c) (WriteRegistersPost [10, 11, 15, 14, 8] [] c jal_80004e10_call.pc fd
      [(10, fd), (11, WhileMinElfParse.trailSlot), (15, -3#64), (14, -1#64), (8, fd), (2, parameterStack)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_mainX5130FSeg ++ caml_mainX513cFSeg ++ caml_mainX5148TSeg ++
        caml_mainX4e08Seg) 0x80005130#64 [(10, fd), (2, parameterStack)] [w] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := camlAttemptRetryTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_main_at_"
        · change guardB bop.BEQ fd (0#64 + Functions.sign_extend (m := 64) 4094#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4094#12 = -2#64 by decide]
          exact beq_eq_false_iff_ne.mpr notTwo
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (parameterStack.toNat + 24)) 8 by
              constructor <;> decide).ld rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (parameterStack.toNat + 24)).toNat = parameterStack.toNat + 24 by decide,
              ← saved]
            exact read8_pins _ _
          · rsk; simp only [wlogM]; trivial
        · change guardB bop.BEQ fd (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
          exact beq_eq_false_iff_ne.mpr notOne
        · change guardB bop.BNE fd (0#64 + Functions.sign_extend (m := 64) 4093#12) = true
          rw [show 0#64 + Functions.sign_extend (m := 64) 4093#12 = -3#64 by decide]
          exact bne_iff_ne.mpr notThree }))
  · rfl
  · rfl
  · simp only [caml_mainX5130FSeg, caml_mainX513cFSeg, caml_mainX5148TSeg, caml_mainX4e08Seg, evalBlocks, evalBlock,
      SegEvalState.init, List.cons_append, List.nil_append]
    rsk
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero,
      show Functions.sign_extend (m := 64) 40#12 = 40#64 by decide]
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    exact ⟨rfl, by decide, by decide⟩
  · rfl
  · decide

theorem caml_read_sections_call (c : Config) (ra fd : BitVec 64) (w : List (BitVec 8)) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (2, parameterStack)])
    (saved : read8 c.σ.mem (parameterStack.toNat + 24) = w)
    (notTwo : fd ≠ -2#64) (notOne : fd ≠ -1#64) (notThree : fd ≠ -3#64) :
    FnSummary 0x80005130#64 (fun d => d = c)
      (WriteRegistersPost ([10, 11, 15, 14, 8] ++ [1]) [] c jal_80004e10_call.target fd
        ((1, jal_80004e10_call.link) ::
          [(10, fd), (11, WhileMinElfParse.trailSlot), (15, -3#64), (14, -1#64), (8, fd), (2, parameterStack)])) :=
  block_then_call c jal_80004e10_call_shape jal_80004e10_call_decode (fun _ h => jal_80004e10_call_pins h)
    (caml_read_sections_front c ra fd w leaf regs saved notTwo notOne notThree) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

def readSectionsSlots (ra s0 s1 s2 : BitVec 64) : List (Nat × BitVec 64) := [(24, ra), (16, s0), (0, s2), (8, s1)]
def readSectionsLog (sp ra s0 s1 s2 : BitVec 64) : List WEntry := nativeWordLog sp 32 (readSectionsSlots ra s0 s1 s2)

theorem readSectionsLog_inside {sp ra s0 s1 s2 : BitVec 64} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (readSectionsLog sp ra s0 s1 s2) :=
  frame.word_log_inside fun off value member => by
    simp only [readSectionsSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member; omega

local macro "nsk" : tactic => `(tactic| simp only [readsectionsnum_line_80004b20, readsectionsnum_line_80004b24, readsectionsnum_line_80004b28, readsectionsnum_line_80004b2c, readsectionsnum_line_80004b30, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

abbrev sectionsWord : List (BitVec 8) := [7#8, 0#8, 0#8, 0#8]

/-- `caml_read_section_descriptors`: open the frame and save `ra`, `s0`, `s2`, `s1`. -/
theorem read_sections_save (c : Config) (sp ra fd s0 s1 s2 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ [(2, sp), (1, ra), (8, s0), (18, s2), (9, s1), (10, fd)]) :
    FnSummary 0x80004b0c#64 (fun e => e = c) (WriteRegistersPost [2] (readSectionsLog sp ra s0 s1 s2) c
      0x80004b20#64 fd [(2, nativeStack sp 32), (1, ra), (8, s0), (18, s2), (9, s1), (10, fd)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (readSectionsLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4b0cSeg 0x80004b0c#64
        [(2, sp), (1, ra), (8, s0), (18, s2), (9, s1), (10, fd)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 18, 9, 10]; decide
      shape := by change ChainOK _ [2, 1, 8, 18, 9, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · simp only [caml_read_section_descriptorsX4b0cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readSectionsLog,
      readSectionsSlots, nativeWordLog, List.map, List.nil_append, readsectionsentry_line_80004b0c, readsectionsentry_line_80004b10, readsectionsentry_line_80004b14, readsectionsentry_line_80004b18, readsectionsentry_line_80004b1c]
    rw [show Functions.sign_extend (m := 64) 4064#12 = -BitVec.ofNat 64 32 by decide,
      show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide,
      show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide,
      show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
    rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b0cSeg, evalBlocks, evalBlock, SegEvalState.init, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsentry_line_80004b0c, readsectionsentry_line_80004b10, readsectionsentry_line_80004b14, readsectionsentry_line_80004b18, readsectionsentry_line_80004b1c]
    rw [show Functions.sign_extend (m := 64) 4064#12 = -BitVec.ofNat 64 32 by decide]
    rfl
  · rfl
  · decide

theorem sections_bytes (i : MInstr) (word : i.word = 3445915#32) :
    Functions.sign_extend (m := 64) (Sail.shift_bits_left (Sail.BitVec.extractLsb (bytesVal MKind.lw sectionsWord) 31 0)
      (shamt5Of i)) = 56#64 := by
  rw [shamt5Of, word]; decide

/-- `num_sections * 8` into `s1`, then `caml_stat_alloc(s1)`. -/
theorem read_sections_num (c : Config) (ra fd trail : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (11, trail)]) (window : ReadWindow trail 4)
    (numWord : read4 c.σ.mem trail.toNat = sectionsWord) :
    FnSummary 0x80004b20#64 (fun e => e = c) (WriteRegistersPost [9, 18, 8, 10] [] c jal_80004b34_call.pc 56#64
      [(10, 56#64), (9, 56#64), (8, trail), (18, fd), (11, trail)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4b20Seg 0x80004b20#64
        [(10, fd), (11, trail)] [sectionsWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 11]; decide
      shape := by change ChainOK _ [10, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsNum_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        exact window.lw rfl (by nsk; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
          BitVec.add_zero]) (by rw [← numWord]; exact read4_pins _ _) }))
  · rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b20Seg, evalBlocks, evalBlock, SegEvalState.init, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsnum_line_80004b20, readsectionsnum_line_80004b24, readsectionsnum_line_80004b28, readsectionsnum_line_80004b2c, readsectionsnum_line_80004b30]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero,
      sections_bytes _ rfl, BitVec.add_zero]
  · rfl
  · decide
local macro "ssk" : tactic => `(tactic| simp only [readsectionsseek_line_80004b38, readsectionsseek_line_80004b3c, readsectionsseek_line_80004b40, readsectionsseek_line_80004b44, readsectionsseek_line_80004b48, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "rdk" : tactic => `(tactic| simp only [readsectionsread_line_80004b50, readsectionsread_line_80004b54, readsectionsread_line_80004b58, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "tsk" : tactic => `(tactic| simp only [readsectionstest_line_80004b64, readsectionstest_line_80004b68, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- After `caml_stat_alloc`: store the block in `trail->section`, then
`lseek(fd, -(56 + 16), SEEK_END)`. -/
theorem read_sections_seek_front (c : Config) (ra fd trail blk : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, 56#64), (10, blk), (8, trail), (18, fd)]) (window : WriteWindow (trail + 16#64) 8)
    (outside : ImageOutside [((trail + 16#64).toNat, 8, blk)]) :
    FnSummary 0x80004b38#64 (fun e => e = c) (WriteRegistersPost [10, 12, 11] [((trail + 16#64).toNat, 8, blk)] c
      jal_80004b4c_call.pc fd [(10, fd), (12, 2#64), (11, -72#64), (9, 56#64), (8, trail), (18, fd)]) := by
  apply registers_of_blocks leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4b38Seg 0x80004b38#64
        [(9, 56#64), (10, blk), (8, trail), (18, fd)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 10, 8, 18]; decide
      shape := by change ChainOK _ [9, 10, 8, 18] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsSeek_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        exact window.sd rfl rfl }))
  · simp only [caml_read_section_descriptorsX4b38Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsseek_line_80004b38, readsectionsseek_line_80004b3c, readsectionsseek_line_80004b40, readsectionsseek_line_80004b44, readsectionsseek_line_80004b48]
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide]
    rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b38Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsseek_line_80004b38, readsectionsseek_line_80004b3c, readsectionsseek_line_80004b40, readsectionsseek_line_80004b44, readsectionsseek_line_80004b48]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    exact ⟨by decide, by decide⟩
  · rfl
  · decide

/-- `read(fd, trail->section, 56)`. -/
theorem read_sections_read_front (c : Config) (ra fd trail blk : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, trail), (9, 56#64), (18, fd)]) (window : ReadWindow (trail + 16#64) 8)
    (blkWord : bytesT c.σ.mem (trail + 16#64).toNat 8 = blk) :
    FnSummary 0x80004b50#64 (fun e => e = c) (WriteRegistersPost [10, 12, 11] [] c jal_80004b5c_call.pc fd
      [(10, fd), (12, 56#64), (11, blk), (8, trail), (9, 56#64), (18, fd)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_read_section_descriptorsX4b50Seg 0x80004b50#64
        [(8, trail), (9, 56#64), (18, fd)] [read8 c.σ.mem (trail + 16#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [8, 9, 18]; decide
      shape := by change ChainOK _ [8, 9, 18] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsRead_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        exact window.ld rfl rfl (read8_pins _ _) }))
  · rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b50Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, readsectionsread_line_80004b50, readsectionsread_line_80004b54, readsectionsread_line_80004b58]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero, read8_value,
      blkWord]
  · rfl
  · decide

/-- `read` returned 56 and there are sections: into the swap loop with `i = 0`. -/
theorem read_sections_test (c : Config) (ra trail : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 56#64), (9, 56#64), (8, trail)]) (window : ReadWindow trail 4)
    (numWord : read4 c.σ.mem trail.toNat = sectionsWord) :
    FnSummary 0x80004b60#64 (fun e => e = c) (WriteRegistersPost [14, 15] [] c 0x80004b70#64 56#64
      [(14, 0#64), (15, 7#64), (10, 56#64), (9, 56#64), (8, trail)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_read_section_descriptorsX4b60FSeg ++
        caml_read_section_descriptorsX4b64FSeg) 0x80004b60#64 [(10, 56#64), (9, 56#64), (8, trail)] [sectionsWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 9, 8]; decide
      shape := by change ChainOK _ [10, 9, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := readSectionsTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_read_section_descriptors_at_"
        · tsk; decide
        · refine memFacts_writeLog ?_ (fun _ => ?_)
          · exact window.lw rfl (by tsk; rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
              BitVec.add_zero]) (by rw [← numWord]; exact read4_pins _ _)
          · tsk; simp only [wlogM]; trivial
        · tsk; decide }))
  · rfl
  · rfl
  · simp only [caml_read_section_descriptorsX4b60FSeg, caml_read_section_descriptorsX4b64FSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      List.cons_append, List.nil_append, readsectionstest_line_80004b64, readsectionstest_line_80004b68]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    decide
  · rfl
  · decide
theorem read_sections_num_call (c : Config) (ra fd trail : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (11, trail)]) (window : ReadWindow trail 4)
    (numWord : read4 c.σ.mem trail.toNat = sectionsWord) :
    FnSummary 0x80004b20#64 (fun e => e = c) (WriteRegistersPost ([9, 18, 8, 10] ++ [1]) [] c
      jal_80004b34_call.target 56#64
      ((1, jal_80004b34_call.link) :: [(10, 56#64), (9, 56#64), (8, trail), (18, fd), (11, trail)])) :=
  block_then_call c jal_80004b34_call_shape jal_80004b34_call_decode (fun _ h => jal_80004b34_call_pins h)
    (read_sections_num c ra fd trail leaf regs window numWord) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

theorem read_sections_seek_call (c : Config) (ra fd trail blk : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, 56#64), (10, blk), (8, trail), (18, fd)]) (window : WriteWindow (trail + 16#64) 8)
    (outside : ImageOutside [((trail + 16#64).toNat, 8, blk)]) :
    FnSummary 0x80004b38#64 (fun e => e = c) (WriteRegistersPost ([10, 12, 11] ++ [1])
      [((trail + 16#64).toNat, 8, blk)] c jal_80004b4c_call.target fd
      ((1, jal_80004b4c_call.link) :: [(10, fd), (12, 2#64), (11, -72#64), (9, 56#64), (8, trail), (18, fd)])) :=
  block_then_call c jal_80004b4c_call_shape jal_80004b4c_call_decode (fun _ h => jal_80004b4c_call_pins h)
    (read_sections_seek_front c ra fd trail blk leaf regs window outside) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

theorem read_sections_read_call (c : Config) (ra fd trail blk : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8, trail), (9, 56#64), (18, fd)]) (window : ReadWindow (trail + 16#64) 8)
    (blkWord : bytesT c.σ.mem (trail + 16#64).toNat 8 = blk) :
    FnSummary 0x80004b50#64 (fun e => e = c) (WriteRegistersPost ([10, 12, 11] ++ [1]) [] c
      jal_80004b5c_call.target fd
      ((1, jal_80004b5c_call.link) :: [(10, fd), (12, 56#64), (11, blk), (8, trail), (9, 56#64), (18, fd)])) :=
  block_then_call c jal_80004b5c_call_shape jal_80004b5c_call_decode (fun _ h => jal_80004b5c_call_pins h)
    (read_sections_read_front c ra fd trail blk leaf regs window blkWord) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
