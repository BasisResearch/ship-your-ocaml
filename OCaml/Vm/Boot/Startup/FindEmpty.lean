import OCaml.Vm.Boot.Startup.FindEmptyNormalized
import OCaml.Vm.Boot.Startup.FindEmptyImage
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Read
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findEmptyBlocks : List BBlock := findenv_rX74a8FSeg ++ findenv_rX74b0TSeg

def findEmptyInput (env : BitVec 64) : GRegs := [(9, env), (14, 0#64)]
def findEmptyLoads (env : BitVec 64) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem env.toNat]
def findEmptyRegs (env : BitVec 64) : GRegs := [(10, 0#64), (20, 61#64), (9, env), (14, 0#64)]

local macro "find_empty_nf" : tactic =>
  `(tactic| simp only [findempty_line_800374a8, findempty_line_800374b0,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findEmptyInput, findEmptyLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findEmpty_input {env ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findEmptyInput env)) (window : ReadWindow env 8)
    (empty : bytesT c.σ.mem env.toNat 8 = 0#64) :
    BlockInput findEmptyBlocks 0x800374a8#64 (findEmptyInput env) (findEmptyLoads env c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [9, 14]; decide
  shape := by change ChainOK _ [9, 14] _; decide
  tick := leaf.tick
  facts := by
    have code := findEmpty_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · find_empty_nf
      decide
    · exact window.ld rfl (by find_empty_nf; exact BitVec.add_zero env) (read8_pins _ _)
    · find_empty_nf
      rw [read8_value, empty]
      decide

theorem findEmpty_regs {env c} (empty : bytesT c.σ.mem env.toNat 8 = 0#64) :
    (evalBlocks findEmptyBlocks (SegEvalState.init (findEmptyInput env) (findEmptyLoads env c))).regs = findEmptyRegs env := by
  simp only [findEmptyBlocks, findenv_rX74a8FSeg, findenv_rX74b0TSeg, List.cons_append, List.nil_append,
    evalBlocks, evalBlock, SegEvalState.init]
  find_empty_nf
  rw [read8_value, empty]
  rfl

/-- A null first environment entry selects the not-found return path. -/
theorem find_empty (c : Config) (env ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findEmptyInput env)) (window : ReadWindow env 8)
    (empty : bytesT c.σ.mem env.toNat 8 = 0#64) :
    FnSummary 0x800374a8#64 (fun d => d = c)
      (WriteRegistersPost [20, 10] [] c 0x8003756c#64 0#64 (findEmptyRegs env)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findEmpty_input leaf regs window empty))
  · rfl
  · rfl
  · exact findEmpty_regs empty
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
