import OCaml.Vm.Boot.Startup.AttemptOpenFailTestNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailTestImage
import OCaml.Vm.Boot.Startup.AttemptOpenFailFreeNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailFreeCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenFailFreeImage
import OCaml.Vm.Boot.Startup.AttemptOpenFailMessageNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailMessageCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenFailMessageImage
import OCaml.Vm.Boot.Startup.AttemptOpenFailErrnoNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailErrnoCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenFailCodeNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailCodeImage
import OCaml.Vm.Boot.Startup.AttemptOpenFailEmfileNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFailEmfileImage
import OCaml.Vm.Boot.Startup.AttemptOpenReturnNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenReturnImage
import OCaml.Vm.Boot.Startup.AttemptOpenPrefix
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.OpenSteps
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! caml_attempt_open when `open` fails: `caml_stat_free(truename)`,
`caml_gc_message(0x100, "Cannot open file\n")`, `errno == EMFILE` selects -4,
otherwise -1; restore and return. -/

/-- The format string of the failure message. -/
def cannotOpenFormat : BitVec 64 := 0x800557c0#64

/-- `fd == -1`: keep it in s1 and take the failure branch. -/
theorem attempt_fail_test (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, -1#64)]) :
    FnSummary 0x80004924#64 (fun d => d = c)
      (WriteRegistersPost [15, 9] [] c 0x80004aa8#64 (-1#64) [(9, -1#64), (15, -1#64), (10, -1#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX4924TSeg 0x80004924#64 [(10, -1#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFailTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        change guardB bop.BEQ (-1#64) (0#64 + Functions.sign_extend (m := 64) 4095#12) = true
        decide }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- `caml_stat_free(truename)`. -/
theorem attempt_fail_free (c : Config) (ra sp truename : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(18, truename), (2, sp)]) :
    FnSummary 0x80004aa8#64 (fun d => d = c)
      (WriteRegistersPost ([10] ++ [1]) [] c jal_80004aac_call.target truename
        ((1, jal_80004aac_call.link) :: [(10, truename), (18, truename), (2, sp)])) := by
  apply block_then_call c jal_80004aac_call_shape jal_80004aac_call_decode (fun _ h => jal_80004aac_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenFailFreeSave 0x80004aa8#64 [(18, truename), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 2]; decide
      shape := by change ChainOK _ [18, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFailFree_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · change [(10, truename + 0#64), (18, truename), (2, sp)] = _
    rw [BitVec.add_zero]
  · rfl
  · decide

theorem cannot_open_auipc : 2147502768#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 333207#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 3344#12 = cannotOpenFormat := by decide

/-- `caml_gc_message(0x100, "Cannot open file\n")`. -/
theorem attempt_fail_message (c : Config) (ra sp : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(2, sp)]) :
    FnSummary 0x80004ab0#64 (fun d => d = c)
      (WriteRegistersPost ([10, 11] ++ [1]) [] c jal_80004abc_call.target 0x100#64
        ((1, jal_80004abc_call.link) :: [(10, 0x100#64), (11, cannotOpenFormat), (2, sp)])) := by
  apply block_then_call c jal_80004abc_call_shape jal_80004abc_call_decode (fun _ h => jal_80004abc_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenFailMessageSave 0x80004ab0#64 [(2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2]; decide
      shape := by change ChainOK _ [2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFailMessage_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · simp only [attemptOpenFailMessageSave, evalBlocks, evalBlock, SegEvalState.init, attemptopenfailmessage_line_80004ab0,
      attemptopenfailmessage_line_80004ab4, attemptopenfailmessage_line_80004ab8, runGM, ldsRunM, wlogM, stepGM, stepLdsM,
      stepMemM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of]
    rw [cannot_open_auipc, show 0#64 + Functions.sign_extend (m := 64) 256#12 = 256#64 by decide]
  · rfl
  · decide

/-- `errno != EMFILE`: keep -1. -/
theorem attempt_fail_code_other (c : Config) (ra reent : BitVec 64) (w : List (BitVec 8)) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, reent)]) (window : ReadWindow reent 4) (word : read4 c.σ.mem reent.toNat = w)
    (other : bytesVal .lw w ≠ 24#64) :
    FnSummary 0x80004ac4#64 (fun d => d = c)
      (WriteRegistersPost [15, 14] [] c 0x80004a1c#64 reent [(15, 24#64), (14, bytesVal .lw w), (10, reent)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX4ac4TSeg 0x80004ac4#64 [(10, reent)] [w] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFailCode_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact window.lw rfl (by change reent + 0#64 = reent; rw [BitVec.add_zero])
            (by rw [← word]; exact read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw w) (0#64 + Functions.sign_extend (m := 64) 24#12) = true
          rw [show 0#64 + Functions.sign_extend (m := 64) 24#12 = 24#64 by decide]
          exact bne_iff_ne.mpr other }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX4ac4TSeg, evalBlocks, evalBlock, SegEvalState.init, attemptopenfailcode_line_80004ac4,
      attemptopenfailcode_line_80004ac8, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show 0#64 + Functions.sign_extend (m := 64) 24#12 = 24#64 by decide]
  · rfl
  · decide

/-- `errno == EMFILE`: -4. -/
theorem attempt_fail_code_emfile (c : Config) (ra reent : BitVec 64) (w : List (BitVec 8)) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, reent)]) (window : ReadWindow reent 4) (word : read4 c.σ.mem reent.toNat = w)
    (emfile : bytesVal .lw w = 24#64) :
    FnSummary 0x80004ac4#64 (fun d => d = c)
      (WriteRegistersPost [15, 14, 9] [] c 0x80004a1c#64 reent [(9, -4#64), (15, 24#64), (14, 24#64), (10, reent)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_attempt_openX4ac4FSeg ++ caml_attempt_openX4ad0Seg) 0x80004ac4#64
        [(10, reent)] [w] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFailCode_code leaf.image
        have code2 := attemptOpenFailEmfile_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact window.lw rfl (by change reent + 0#64 = reent; rw [BitVec.add_zero])
            (by rw [← word]; exact read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw w) (0#64 + Functions.sign_extend (m := 64) 24#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 24#12 = 24#64 by decide, emfile]
          decide }))
  · rfl
  · rfl
  · simp only [caml_attempt_openX4ac4FSeg, caml_attempt_openX4ad0Seg, evalBlocks, evalBlock, SegEvalState.init,
      attemptopenfailcode_line_80004ac4, attemptopenfailcode_line_80004ac8, attemptopenfailemfile_line_80004ad0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons_append, List.nil_append]
    rw [show 0#64 + Functions.sign_extend (m := 64) 24#12 = 24#64 by decide,
      show 0#64 + Functions.sign_extend (m := 64) 4092#12 = -4#64 by decide, emfile]
  · rfl
  · decide

/-- Restore caml_attempt_open's saves and return `fd`. -/
theorem attempt_open_return (c : Config) (sp ra s0 s1 s2 s3 s4 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ [(2, nativeStack sp 64), (9, v)])
    (saved : ∀ off value, (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4 →
      bytesT c.σ.mem (nativeFrameBase sp 64 + off) 8 = value)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80004a1c#64 (fun e => e = c)
      (WriteRegistersPost [1, 8, 18, 19, 20, 10, 9, 2] [] c ra v
        [(2, sp), (9, s1), (10, v), (20, s4), (19, s3), (18, s2), (8, s0), (1, ra)]) := by
  have word (off : Nat) (value : BitVec 64) (member : (off, value) ∈ attemptOpenSlots ra s0 s1 s2 s3 s4) :
      bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + off)) = value := by
    rw [read8_value]; exact saved off value member
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_attempt_openX4a1cSeg 0x80004a1c#64 [(2, nativeStack sp 64), (9, v)]
        [read8 c.σ.mem (nativeFrameBase sp 64 + 56), read8 c.σ.mem (nativeFrameBase sp 64 + 48),
          read8 c.σ.mem (nativeFrameBase sp 64 + 32), read8 c.σ.mem (nativeFrameBase sp 64 + 24),
          read8 c.σ.mem (nativeFrameBase sp 64 + 16), read8 c.σ.mem (nativeFrameBase sp 64 + 40)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 9]; decide
      shape := by change ChainOK _ [2, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 56 ra (by simp [attemptOpenSlots]), ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 64 + 56)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [word 56 ra (by simp [attemptOpenSlots]), ret_tgt ra aligned]
  · simp only [caml_attempt_openX4a1cSeg, evalBlocks, evalBlock, SegEvalState.init, attemptopenreturn_line_80004a1c, attemptopenreturn_line_80004a20, attemptopenreturn_line_80004a24, attemptopenreturn_line_80004a28, attemptopenreturn_line_80004a2c, attemptopenreturn_line_80004a30, attemptopenreturn_line_80004a34, attemptopenreturn_line_80004a38, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, nativeStack_restore,
      word 40 s1 (by simp [attemptOpenSlots]), word 16 s4 (by simp [attemptOpenSlots]),
      word 24 s3 (by simp [attemptOpenSlots]), word 32 s2 (by simp [attemptOpenSlots]),
      word 48 s0 (by simp [attemptOpenSlots]), word 56 ra (by simp [attemptOpenSlots]),
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
