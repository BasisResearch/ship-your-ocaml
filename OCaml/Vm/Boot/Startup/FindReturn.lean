import OCaml.Vm.Boot.Startup.FindReturnNormalized
import OCaml.Vm.Boot.Startup.FindReturnImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Boot.Startup.NativeRead
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findReturnInput (sp : BitVec 64) : GRegs := [(2, nativeStack sp 80)]
def findReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 80 + 72), read8 c.σ.mem (nativeFrameBase sp 80 + 56),
   read8 c.σ.mem (nativeFrameBase sp 80 + 48), read8 c.σ.mem (nativeFrameBase sp 80 + 40),
   read8 c.σ.mem (nativeFrameBase sp 80 + 24), read8 c.σ.mem (nativeFrameBase sp 80 + 16)]
def findReturnRegs (sp ra s1 s2 s3 s5 s6 : BitVec 64) : GRegs :=
  [(2, sp), (10, 0#64), (22, s6), (21, s5), (19, s3), (18, s2), (9, s1), (1, ra)]

structure FindReturnSaved (sp ra s1 s2 s3 s5 s6 : BitVec 64) (c : Config) : Prop where
  caller : bytesT c.σ.mem (nativeFrameBase sp 80 + 72) 8 = ra
  saved1 : bytesT c.σ.mem (nativeFrameBase sp 80 + 56) 8 = s1
  saved2 : bytesT c.σ.mem (nativeFrameBase sp 80 + 48) 8 = s2
  saved3 : bytesT c.σ.mem (nativeFrameBase sp 80 + 40) 8 = s3
  saved5 : bytesT c.σ.mem (nativeFrameBase sp 80 + 24) 8 = s5
  saved6 : bytesT c.σ.mem (nativeFrameBase sp 80 + 16) 8 = s6

local macro "find_return_nf" : tactic =>
  `(tactic| simp only [findreturn_line_800374fc, findreturn_line_80037500, findreturn_line_80037504,
    findreturn_line_80037508, findreturn_line_8003750c, findreturn_line_80037510,
    findreturn_line_80037514, findreturn_line_80037518,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findReturnInput, findReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findReturn_input {sp ra s1 s2 s3 s5 s6 oldra c} (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findReturnInput sp))
    (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c) (aligned : ra.toNat % 4 = 0) :
    BlockInput findenv_rX74fcSeg 0x800374fc#64 (findReturnInput sp) (findReturnLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2]; decide
  shape := by change ChainOK _ [2] _; decide
  tick := leaf.tick
  facts := by
    have code := findReturn_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · exact (frame.read_slot (off := 72) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · find_return_nf
      rw [read8_value, saved.caller]
      simpa only [ret_tgt ra aligned] using aligned

/-- Restore the environment-search caller frame and return a null result. -/
theorem find_return (c : Config) (sp ra s1 s2 s3 s5 s6 oldra : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findReturnInput sp)) (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800374fc#64 (fun d => d = c)
      (WriteRegistersPost [1, 9, 18, 19, 21, 22, 10, 2] [] c ra 0#64 (findReturnRegs sp ra s1 s2 s3 s5 s6)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findReturn_input leaf frame regs saved aligned))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, saved.caller]
    exact ret_tgt ra aligned
  · simp only [findenv_rX74fcSeg, evalBlocks, evalBlock, SegEvalState.init]
    find_return_nf
    rw [read8_value, read8_value, read8_value, read8_value, read8_value, read8_value,
      saved.caller, saved.saved1, saved.saved2, saved.saved3, saved.saved5, saved.saved6]
    change [(2, nativeStack sp 80 + 80#64), (10, 0#64), (22, s6), (21, s5), (19, s3), (18, s2), (9, s1), (1, ra)] = _
    rw [nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
