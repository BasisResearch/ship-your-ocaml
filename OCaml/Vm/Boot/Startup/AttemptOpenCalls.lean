import OCaml.Vm.Boot.Startup.AttemptOpenStrdupNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenStrdupCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenMessageNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenMessageCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenFreeCopyNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenFreeCopyCallInterface
import OCaml.Vm.Boot.Startup.AttemptOpenOpenNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenOpenCallInterface
import OCaml.Vm.Boot.Startup.BlockCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! caml_attempt_open after the search: `u_truename = caml_stat_strdup(truename)`,
`caml_gc_message(0x100, "Opening bytecode executable %s\n", u_truename)`,
`caml_stat_free(u_truename)`, `open(truename, O_RDONLY)`. -/

/-- The format string of the opening message. -/
def openingFormat : BitVec 64 := 0x800557a0#64

/-- Keep `truename` in s2 and call `caml_stat_strdup(truename)`. -/
theorem attempt_open_strdup (c : Config) (ra sp truename : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, truename), (2, sp)]) :
    FnSummary 0x800048f0#64 (fun d => d = c)
      (WriteRegistersPost ([18] ++ [1]) [] c jal_800048f4_call.target truename
        ((1, jal_800048f4_call.link) :: [(18, truename), (10, truename), (2, sp)])) := by
  apply block_then_call c jal_800048f4_call_shape jal_800048f4_call_decode (fun _ h => jal_800048f4_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenStrdupSave 0x800048f0#64 [(10, truename), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenStrdup_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · change [(18, truename + 0#64), (10, truename), (2, sp)] = _
    rw [BitVec.add_zero]
  · rfl
  · decide

/-- Keep the copy in s1 and call `caml_gc_message(0x100, fmt, copy)`. -/
theorem attempt_open_message (c : Config) (ra sp copy : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, copy), (2, sp)]) :
    FnSummary 0x800048f8#64 (fun d => d = c)
      (WriteRegistersPost ([12, 9, 11, 10] ++ [1]) [] c jal_8000490c_call.target 0x100#64
        ((1, jal_8000490c_call.link) :: [(10, 0x100#64), (11, openingFormat), (9, copy), (12, copy), (2, sp)])) := by
  apply block_then_call c jal_8000490c_call_shape jal_8000490c_call_decode (fun _ h => jal_8000490c_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenMessageSave 0x800048f8#64 [(10, copy), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenMessage_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · simp only [attemptOpenMessageSave, evalBlocks, evalBlock, SegEvalState.init, attemptopenmessage_line_800048f8,
      attemptopenmessage_line_800048fc, attemptopenmessage_line_80004900, attemptopenmessage_line_80004904,
      attemptopenmessage_line_80004908, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG,
      eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, List.cons.injEq, Prod.mk.injEq]
    have zero : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide
    rw [zero, BitVec.add_zero]
    exact ⟨⟨trivial, by decide⟩, ⟨trivial, by decide⟩, ⟨trivial, rfl⟩, ⟨trivial, rfl⟩, trivial⟩
  · rfl
  · decide

/-- `caml_stat_free(copy)`. -/
theorem attempt_open_free_copy (c : Config) (ra sp copy : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9, copy), (2, sp)]) :
    FnSummary 0x80004910#64 (fun d => d = c)
      (WriteRegistersPost ([10] ++ [1]) [] c jal_80004914_call.target copy
        ((1, jal_80004914_call.link) :: [(10, copy), (9, copy), (2, sp)])) := by
  apply block_then_call c jal_80004914_call_shape jal_80004914_call_decode (fun _ h => jal_80004914_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenFreeCopySave 0x80004910#64 [(9, copy), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 2]; decide
      shape := by change ChainOK _ [9, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenFreeCopy_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · change [(10, copy + 0#64), (9, copy), (2, sp)] = _
    rw [BitVec.add_zero]
  · rfl
  · decide

/-- `open(truename, O_RDONLY)`. -/
theorem attempt_open_open (c : Config) (ra sp truename : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(18, truename), (2, sp)]) :
    FnSummary 0x80004918#64 (fun d => d = c)
      (WriteRegistersPost ([10, 11] ++ [1]) [] c jal_80004920_call.target truename
        ((1, jal_80004920_call.link) :: [(11, 0#64), (10, truename), (18, truename), (2, sp)])) := by
  apply block_then_call c jal_80004920_call_shape jal_80004920_call_decode (fun _ h => jal_80004920_call_pins h)
    _ (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput attemptOpenOpenSave 0x80004918#64 [(18, truename), (2, sp)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 2]; decide
      shape := by change ChainOK _ [18, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := attemptOpenOpen_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_" }))
  · rfl
  · rfl
  · change [(11, 0#64 + 0#64), (10, truename + 0#64), (18, truename), (2, sp)] = _
    rw [BitVec.add_zero, BitVec.add_zero]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
