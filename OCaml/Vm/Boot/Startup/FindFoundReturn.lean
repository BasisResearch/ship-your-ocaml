import OCaml.Vm.Boot.Startup.FindFoundReturnNormalized
import OCaml.Vm.Boot.Startup.FindFoundReturnImage
import OCaml.Vm.Boot.Startup.FindReturn
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findFoundReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 80 + 8), read8 c.σ.mem (nativeFrameBase sp 80 + 64), read8 c.σ.mem (nativeFrameBase sp 80 + 72), read8 c.σ.mem (nativeFrameBase sp 80 + 32), read8 c.σ.mem (nativeFrameBase sp 80 + 56), read8 c.σ.mem (nativeFrameBase sp 80 + 48), read8 c.σ.mem (nativeFrameBase sp 80 + 40), read8 c.σ.mem (nativeFrameBase sp 80 + 24), read8 c.σ.mem (nativeFrameBase sp 80 + 16)]
def findFoundReturnRegs (sp ra s0 s1 s2 s3 s4 s5 s6 pointer : BitVec 64) : GRegs :=
  [(2, sp), (10, pointer + 1#64), (22, s6), (21, s5), (19, s3), (18, s2), (9, s1), (20, s4), (1, ra), (8, s0), (15, pointer)]

local macro "find_found_return_nf" : tactic =>
  `(tactic| simp only [findfoundreturn_line_8003753c, findfoundreturn_line_80037540, findfoundreturn_line_80037544, findfoundreturn_line_80037548, findfoundreturn_line_8003754c, findfoundreturn_line_80037550, findfoundreturn_line_80037554, findfoundreturn_line_80037558, findfoundreturn_line_8003755c, findfoundreturn_line_80037560, findfoundreturn_line_80037564,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findReturnInput, findFoundReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findFoundReturn_input {sp ra s0 s1 s2 s3 s4 s5 s6 pointer oldra c} (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findReturnInput sp)) (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0)
    (saved4 : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4)
    (savedPointer : bytesT c.σ.mem (nativeFrameBase sp 80 + 8) 8 = pointer)
    (aligned : ra.toNat % 4 = 0) :
    BlockInput findenv_rX753cSeg 0x8003753c#64 (findReturnInput sp) (findFoundReturnLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2]; decide
  shape := by change ChainOK _ [2] _; decide
  tick := leaf.tick
  facts := by
    have code := findFoundReturn_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 64) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 72) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
      rw [read8_value, saved.caller, ret_tgt ra aligned]
      exact aligned

/-- The successful search epilogue restores every saved register and returns
one byte past the matching equals sign. -/
theorem find_found_return (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 pointer oldra : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findReturnInput sp)) (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 c)
    (saved0 : bytesT c.σ.mem (nativeFrameBase sp 80 + 64) 8 = s0)
    (saved4 : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4)
    (savedPointer : bytesT c.σ.mem (nativeFrameBase sp 80 + 8) 8 = pointer)
    (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8003753c#64 (fun d => d = c)
      (WriteRegistersPost [15, 8, 1, 20, 9, 18, 19, 21, 22, 10, 2] [] c ra (pointer + 1#64)
        (findFoundReturnRegs sp ra s0 s1 s2 s3 s4 s5 s6 pointer)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findFoundReturn_input leaf frame regs saved saved0 saved4 savedPointer aligned))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, saved.caller]
    exact ret_tgt ra aligned
  · simp only [findenv_rX753cSeg, evalBlocks, evalBlock, SegEvalState.init]
    find_found_return_nf
    simp only [read8_value, savedPointer, saved0, saved4, saved.caller, saved.saved1,
      saved.saved2, saved.saved3, saved.saved5, saved.saved6]
    change [(2, nativeStack sp 80 + 80#64), (10, pointer + 1#64), (22, s6), (21, s5),
      (19, s3), (18, s2), (9, s1), (20, s4), (1, ra), (8, s0), (15, pointer)] = _
    rw [nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
