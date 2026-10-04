import OCaml.Vm.Boot.Startup.StatCheckedPrefixNormalized
import OCaml.Vm.Boot.Startup.StatCheckedPrefixImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def statCheckedLog (sp ra s0 : BitVec 64) : List WEntry :=
  nativeWordLog sp 32 [(16, s0), (24, ra)]
def statCheckedRegs (sp ra n : BitVec 64) : GRegs :=
  [(8, n), (2, nativeStack sp 32), (15, 0#64), (1, ra), (10, n)]
structure StatCheckedPrefixInput (sp ra s0 n : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  frame : NativeFrame sp 32
  regs : GHolds c.σ (caml_stat_allocXbb2cTL sp s0 ra n)
  pool : LPins8 c.σ.mem Layout.sym_pool (List.replicate 8 0#8)

theorem statCheckedLog_inside {sp ra s0} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (statCheckedLog sp ra s0) := by
  apply frame.word_log_inside
  intro off value member
  have cases' : (off, value) = (16, s0) ∨ (off, value) = (24, ra) := by simpa using member
  rcases cases' with eq | eq <;> cases eq <;> decide

local macro "stat_checked_nf" : tactic =>
  `(tactic| simp only [statcheckedprefix_line_8000bb2c, statcheckedprefix_line_8000bb30,
    statcheckedprefix_line_8000bb34, statcheckedprefix_line_8000bb38,
    statcheckedprefix_line_8000bb3c, statcheckedprefix_line_8000bb40,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    caml_stat_allocXbb2cTL, wvalM, wentryM, widthOfM, imm20Of,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem statCheckedPrefix_input {sp ra s0 n c} (h : StatCheckedPrefixInput sp ra s0 n c) :
    BlockInput caml_stat_allocXbb2cTSeg 0x8000bb2c#64
      (caml_stat_allocXbb2cTL sp s0 ra n) [List.replicate 8 0#8] c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [2, 8, 1, 10]; decide
  shape := by change ChainOK _ [2, 8, 1, 10] _; decide
  tick := h.tick
  facts := by
    have code := statCheckedPrefix_code h.image
    have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, h.frame.address _ (by omega)]
      exact h.frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_at_"
    · apply (show ReadWindow (BitVec.ofNat 64 Layout.sym_pool) 8 from by constructor <;> decide).ld rfl
      · stat_checked_nf
        rfl
      · exact h.pool
    · exact (slot 16 (by decide) (by decide)).sd rfl rfl
    · exact (slot 24 (by decide) (by decide)).sd rfl rfl
    · rfl

/-- Pooling disabled: save the caller and dispatch to the landed malloc summary. -/
theorem stat_checked_prefix (c : Config) (sp ra s0 n : BitVec 64)
    (h : StatCheckedPrefixInput sp ra s0 n c) :
    FnSummary 0x8000bb2c#64 (fun d => d = c)
      (WriteRegistersPost [15, 2, 8] (statCheckedLog sp ra s0) c 0x8000bb88#64 n
        (statCheckedRegs sp ra n)) := by
  apply registers_of_blocks h.image (h.frame.image_outside (statCheckedLog_inside h.frame))
    (block_summary _ _ _ _ _ (statCheckedPrefix_input h))
  · rfl
  · rfl
  · simp only [caml_stat_allocXbb2cTSeg, evalBlocks, evalBlock, SegEvalState.init]
    stat_checked_nf
    change [(8, n + 0#64), (2, nativeStack sp 32), (15, 0#64), (1, ra), (10, n)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
