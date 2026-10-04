import OCaml.Vm.Boot.Startup.GetenvReturnNormalized
import OCaml.Vm.Boot.Startup.GetenvReturnImage
import OCaml.Vm.Boot.Startup.NativeRead
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def getenvReturnInput (sp : BitVec 64) (value : BitVec 64 := 0#64) : GRegs := [(2, nativeStack sp 32), (10, value)]
def getenvReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem (nativeFrameBase sp 32 + 24)]
def getenvReturnRegs (sp ra : BitVec 64) (value : BitVec 64 := 0#64) : GRegs := [(2, sp), (1, ra), (10, value)]

local macro "getenv_return_nf" : tactic =>
  `(tactic| simp only [getenvreturn_line_8003742c, getenvreturn_line_80037430,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    getenvReturnInput, getenvReturnLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem getenvReturn_input {sp ra oldra value c} (leaf : LeafInput oldra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ (getenvReturnInput sp value))
    (saved : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra) (aligned : ra.toNat % 4 = 0) :
    BlockInput getenvX742cSeg 0x8003742c#64 (getenvReturnInput sp value) (getenvReturnLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 10]; decide
  shape := by change ChainOK _ [2, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := getenvReturn_code leaf.image
    chain_facts code with "Vsa.Sim.Code.getenv_at_"
    · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
    · getenv_return_nf
      rw [read8_value, saved, ret_tgt ra aligned]
      exact aligned

/-- Getenv restores its own caller link and stack after either search result. -/
theorem getenv_return (c : Config) (sp ra oldra : BitVec 64) {value : BitVec 64} (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ (getenvReturnInput sp value))
    (saved : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8003742c#64 (fun d => d = c)
      (WriteRegistersPost [1, 2] [] c ra value (getenvReturnRegs sp ra value)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (getenvReturn_input leaf frame regs saved aligned))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, saved]
    exact ret_tgt ra aligned
  · change [(2, nativeStack sp 32 + 32#64), (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24))), (10, value)] = _
    rw [read8_value, saved, nativeStack_restore]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
