import OCaml.Vm.Boot.Startup.StatCheckedReturnNormalized
import OCaml.Vm.Boot.Startup.StatCheckedReturnImage
import OCaml.Vm.Boot.Startup.StatCheckedTestRows
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def statCheckedReturnBlocks : List BBlock := caml_stat_allocXbb8cTSeg ++ caml_stat_allocXbb78Seg
def statCheckedReturnInput (sp p : BitVec 64) : GRegs := [(2, nativeStack sp 32), (10, p)]
def statCheckedReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 32 + 24), read8 c.σ.mem (nativeFrameBase sp 32 + 16)]
def statCheckedReturnRegs (sp ra s0 p : BitVec 64) : GRegs := [(2, sp), (8, s0), (1, ra), (10, p)]

local macro "stat_checked_return_nf" : tactic =>
  `(tactic| simp only [statcheckedreturn_line_8000bb78, statcheckedreturn_line_8000bb7c,
    statcheckedreturn_line_8000bb80, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, statCheckedReturnInput, statCheckedReturnLoads,
    wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some,
    Nat.reduceEqDiff, ite_true, ite_false])

structure StatCheckedReturnInput (sp ra s0 p oldra : BitVec 64) (c : Config) : Prop extends LeafInput oldra c where
  frame : NativeFrame sp 32
  regs : GHolds c.σ (statCheckedReturnInput sp p)
  nonzero : p ≠ 0#64
  savedRa : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra
  savedS0 : bytesT c.σ.mem (nativeFrameBase sp 32 + 16) 8 = s0
  returnAligned : ra.toNat % 4 = 0

theorem statCheckedReturn_input {sp ra s0 p oldra c} (h : StatCheckedReturnInput sp ra s0 p oldra c) :
    BlockInput statCheckedReturnBlocks 0x8000bb8c#64
      (statCheckedReturnInput sp p) (statCheckedReturnLoads sp c) c where
  good := h.good
  minstret := h.minstret
  regs := h.regs
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := h.tick
  facts := by
    have code := statCheckedReturn_code h.image
    chain_facts code with "Vsa.Sim.Code.caml_stat_alloc_at_"
    · change (p != 0#64) = true
      exact bne_iff_ne.mpr h.nonzero
    · exact (h.frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (h.frame.pins_slot c (by decide))
    · stat_checked_return_nf
      exact (h.frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (h.frame.pins_slot c (by decide))
    · stat_checked_return_nf
      rw [read8_value, h.savedRa, ret_tgt ra h.returnAligned]
      exact h.returnAligned

/-- Successful checked allocation restores both caller words and returns the fresh pointer. -/
theorem stat_checked_return (c : Config) (sp ra s0 p oldra : BitVec 64)
    (h : StatCheckedReturnInput sp ra s0 p oldra c) :
    FnSummary 0x8000bb8c#64 (fun d => d = c)
      (WriteRegistersPost [1, 8, 2] [] c ra p (statCheckedReturnRegs sp ra s0 p)) := by
  apply registers_of_blocks h.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (statCheckedReturn_input h))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, h.savedRa]
    exact ret_tgt ra h.returnAligned
  · change [(2, nativeStack sp 32 + 32#64),
      (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 16))),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24))), (10, p)] = _
    rw [read8_value, read8_value, h.savedRa, h.savedS0, nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
