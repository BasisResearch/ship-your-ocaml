import OCaml.Vm.Boot.Startup.StrncmpDispatchNormalized
import OCaml.Vm.Boot.Startup.StrncmpDispatchImage
import OCaml.Vm.Boot.Startup.StrncmpFirst
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def strncmpDispatchBlocks : List BBlock := strncmpX0cc8FSeg ++ strncmpX0cccTSeg

def strncmpAlignment (p q : BitVec 64) : BitVec 64 := (p ||| q) &&& 7#64

theorem strncmpDispatch_input {p q n ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q n)) (positive : n ≠ 0#64)
    (unaligned : strncmpAlignment p q ≠ 0#64) :
    BlockInput strncmpDispatchBlocks 0x80040cc8#64 (strncmpFirstInput p q n) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12]; decide
  shape := by change ChainOK _ [10, 11, 12] _; decide
  tick := leaf.tick
  facts := by
    have code := strncmpDispatch_code leaf.image
    chain_facts code with "Vsa.Sim.Code.strncmp_at_"
    · exact beq_eq_false_iff_ne.mpr positive
    · change (strncmpAlignment p q != 0#64) = true
      exact bne_iff_ne.mpr unaligned

/-- Positive bounded comparison uses the byte path whenever either pointer is unaligned. -/
theorem strncmp_dispatch (c : Config) (p q n ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q n)) (positive : n ≠ 0#64)
    (unaligned : strncmpAlignment p q ≠ 0#64) :
    FnSummary 0x80040cc8#64 (fun d => d = c)
      (WriteRegistersPost [15] [] c 0x80040d3c#64 p
        ((15, strncmpAlignment p q) :: strncmpFirstInput p q n)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpDispatch_input leaf regs positive unaligned))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
