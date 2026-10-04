import OCaml.Vm.Boot.Startup.FindEmptyNormalized
import OCaml.Vm.Boot.Startup.FindEmptyImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Read
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findLoadedBlocks : List BBlock := findenv_rX74a8FSeg ++ findenv_rX74b0FSeg

def findLoadedInput (env : BitVec 64) : GRegs := [(9, env), (14, 0#64)]
def findLoadedLoads (env : BitVec 64) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem env.toNat]
def findLoadedRegs (env entry : BitVec 64) : GRegs := [(10, entry), (20, 61#64), (9, env), (14, 0#64)]

local macro "find_loaded_nf" : tactic =>
  `(tactic| simp only [findempty_line_800374a8, findempty_line_800374b0,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findLoadedInput, findLoadedLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findLoaded_input {env entry ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findLoadedInput env)) (window : ReadWindow env 8)
    (word : bytesT c.σ.mem env.toNat 8 = entry) (nonnull : entry ≠ 0#64) :
    BlockInput findLoadedBlocks 0x800374a8#64 (findLoadedInput env) (findLoadedLoads env c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [9, 14]; decide
  shape := by change ChainOK _ [9, 14] _; decide
  tick := leaf.tick
  facts := by
    have code := findEmpty_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · find_loaded_nf
      decide
    · exact window.ld rfl (by find_loaded_nf; exact BitVec.add_zero env) (read8_pins _ _)
    · find_loaded_nf
      rw [read8_value, word]
      exact beq_eq_false_iff_ne.mpr nonnull

theorem findLoaded_regs {env entry c} (word : bytesT c.σ.mem env.toNat 8 = entry) (nonnull : entry ≠ 0#64) :
    (evalBlocks findLoadedBlocks (SegEvalState.init (findLoadedInput env) (findLoadedLoads env c))).regs = findLoadedRegs env entry := by
  simp only [findLoadedBlocks, findenv_rX74a8FSeg, findenv_rX74b0FSeg, List.cons_append, List.nil_append,
    evalBlocks, evalBlock, SegEvalState.init]
  find_loaded_nf
  rw [read8_value, word]
  rfl

/-- A nonnull first environment entry selects the bounded name comparison. -/
theorem find_loaded (c : Config) (env entry ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findLoadedInput env)) (window : ReadWindow env 8)
    (word : bytesT c.σ.mem env.toNat 8 = entry) (nonnull : entry ≠ 0#64) :
    FnSummary 0x800374a8#64 (fun d => d = c)
      (WriteRegistersPost [20, 10] [] c 0x800374b8#64 entry (findLoadedRegs env entry)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findLoaded_input leaf regs window word nonnull))
  · rfl
  · rfl
  · exact findLoaded_regs word nonnull
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
