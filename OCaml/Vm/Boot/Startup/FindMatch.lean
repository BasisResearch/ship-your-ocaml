import OCaml.Vm.Boot.Startup.FindMatchNormalized
import OCaml.Vm.Boot.Startup.FindMatchImage
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findMatchBlocks : List BBlock := findenv_rX74ccFSeg ++ findenv_rX74d0TSeg

def findMatchInput (env count : BitVec 64) : GRegs := [(10, 0#64), (9, env), (8, count), (20, 61#64)]
def findMatchLoads (env : BitVec 64) (c : Config) : List (List (BitVec 8)) := [read8 c.σ.mem env.toNat, [61#8]]
def findMatchRegs (env entry count : BitVec 64) : GRegs :=
  [(14, 61#64), (15, entry + count), (10, 0#64), (9, env), (8, count), (20, 61#64)]

local macro "find_match_nf" : tactic =>
  `(tactic| simp only [findmatch_line_800374d0, findmatch_line_800374d4, findmatch_line_800374d8,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    findMatchInput, findMatchLoads, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findMatch_input {env entry count ra c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findMatchInput env count)) (array : ReadWindow env 8)
    (first : bytesT c.σ.mem env.toNat 8 = entry) (window : ReadWindow (entry + count) 1)
    (equals : (c.σ.mem[(entry + count).toNat]?).getD 0 = 61#8) :
    BlockInput findMatchBlocks 0x800374cc#64 (findMatchInput env count) (findMatchLoads env c) c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 9, 8, 20]; decide
  shape := by change ChainOK _ [10, 9, 8, 20] _; decide
  tick := leaf.tick
  facts := by
    have code := findMatch_code leaf.image
    chain_facts code with "Vsa.Sim.Code._findenv_r_at_"
    · change (0#64 != 0#64) = false
      rfl
    · exact array.ld rfl (BitVec.add_zero env) (read8_pins _ _)
    · apply window.lbu rfl
      · find_match_nf
        rw [read8_value, first]
        exact BitVec.add_zero _
      · exact equals
    · find_match_nf
      decide

/-- Equal bounded names followed by '=' select the successful lookup return. -/
theorem find_match (c : Config) (env entry count ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (findMatchInput env count)) (array : ReadWindow env 8)
    (first : bytesT c.σ.mem env.toNat 8 = entry) (window : ReadWindow (entry + count) 1)
    (equals : (c.σ.mem[(entry + count).toNat]?).getD 0 = 61#8) :
    FnSummary 0x800374cc#64 (fun d => d = c)
      (WriteRegistersPost [15, 14] [] c 0x80037520#64 0#64 (findMatchRegs env entry count)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (findMatch_input leaf regs array first window equals))
  · rfl
  · rfl
  · change [(14, 61#64), (15, bytesVal .ld (read8 c.σ.mem env.toNat) + count),
      (10, 0#64), (9, env), (8, count), (20, 61#64)] = _
    rw [read8_value, first]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
