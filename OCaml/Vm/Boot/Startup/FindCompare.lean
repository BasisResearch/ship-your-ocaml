import OCaml.Vm.Boot.Startup.FindCompareNormalized
import OCaml.Vm.Boot.Startup.FindCompareCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findCompareCount (name cursor : BitVec 64) : BitVec 64 :=
  Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb cursor 31 0 - Sail.BitVec.extractLsb name 31 0)
def findCompareInput (sp s0 name cursor entry : BitVec 64) : GRegs :=
  [(2, nativeStack sp 80), (8, s0), (12, cursor), (18, name), (10, entry)]
def findCompareLog (sp s0 : BitVec 64) : List WEntry := nativeWordLog sp 80 [(64, s0)]
def findCompareRegs (sp name cursor entry : BitVec 64) : GRegs :=
  [(11, name), (12, findCompareCount name cursor), (8, findCompareCount name cursor),
   (2, nativeStack sp 80), (18, name), (10, entry)]

theorem findCompare_input {sp s0 name cursor entry ra c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findCompareInput sp s0 name cursor entry)) :
    BlockInput findenv_rX74b8Seg 0x800374b8#64 (findCompareInput sp s0 name cursor entry) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 8, 12, 18, 10]; decide
  shape := by change ChainOK _ [2, 8, 12, 18, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := findCompare_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    have window : WriteWindow (nativeStack sp 80 + 64#64) 8 := by
      rw [nativeStack, frame.address 64 (by decide)]
      exact frame.word (by decide) (by decide)
    exact window.sd rfl rfl

theorem findCompareLog_inside {sp s0} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (findCompareLog sp s0) := by
  apply frame.word_log_inside
  intro off value member
  have eq : (off, value) = (64, s0) := List.mem_singleton.mp member
  cases eq
  decide

/-- Preserve s0 and prepare the exact bounded-comparison arguments from the
already-scanned name cursor. -/
theorem find_compare (c : Config) (sp s0 name cursor entry ra : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findCompareInput sp s0 name cursor entry)) :
    FnSummary 0x800374b8#64 (fun d => d = c)
      (WriteRegistersPost [8, 12, 11] (findCompareLog sp s0) c jal_800374c8_call.pc entry
        (findCompareRegs sp name cursor entry)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (findCompareLog_inside frame))
    (block_summary _ _ _ _ _ (findCompare_input leaf frame regs))
  · rfl
  · rfl
  · change [(11, name + 0#64), (12, findCompareCount name cursor + 0#64),
      (8, findCompareCount name cursor), (2, nativeStack sp 80), (18, name), (10, entry)] = _
    simp only [BitVec.add_zero]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
