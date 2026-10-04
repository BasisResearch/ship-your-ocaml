import OCaml.Vm.Boot.Startup.FindRestoreNormalized
import OCaml.Vm.Boot.Startup.FindRestoreImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Boot.Startup.NativeRead
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findRestoreInput (sp reent : BitVec 64) : GRegs := [(2, nativeStack sp 80), (21, reent), (10, 0#64)]
def findRestoreLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem (nativeFrameBase sp 80 + 32)]
def findRestoreRegs (sp reent s4 : BitVec 64) : GRegs := [(20, s4), (2, nativeStack sp 80), (21, reent), (10, 0#64)]

theorem findRestore_input {sp reent ra c} (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findRestoreInput sp reent)) :
    BlockInput findenv_rX756cSeg 0x8003756c#64 (findRestoreInput sp reent) (findRestoreLoads sp c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 21, 10]; decide
  shape := by change ChainOK _ [2, 21, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := findRestore_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))

/-- Restore s4 after the environment name scan before the common unlock path. -/
theorem find_restore (c : Config) (sp reent s4 ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findRestoreInput sp reent))
    (saved : bytesT c.σ.mem (nativeFrameBase sp 80 + 32) 8 = s4) :
    FnSummary 0x8003756c#64 (fun d => d = c)
      (WriteRegistersPost [20] [] c 0x800374f4#64 0#64 (findRestoreRegs sp reent s4)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findRestore_input leaf frame regs))
  · rfl
  · rfl
  · change [(20, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 32))),
      (2, nativeStack sp 80), (21, reent), (10, 0#64)] = _
    rw [read8_value, saved]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
