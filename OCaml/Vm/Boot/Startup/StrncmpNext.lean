import OCaml.Vm.Boot.Startup.StrncmpNextNormalized
import OCaml.Vm.Boot.Startup.StrncmpNextImage
import OCaml.Vm.Boot.Startup.StrncmpFirst
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def strncmpNextBlocks : List BBlock := strncmpX0d54FSeg ++ strncmpX0d5cFSeg

def strncmpNextInput (p q stop : BitVec 64) (previous : BitVec 8) : GRegs :=
  [(10, p), (11, q), (12, stop), (15, nameByteWord previous)]
def strncmpNextRegs (p q stop : BitVec 64) (b : BitVec 8) : GRegs :=
  [(14, nameByteWord b), (15, nameByteWord b), (10, p + 1#64), (11, q), (12, stop)]

local macro "strncmp_next_nf" : tactic =>
  `(tactic| simp only [strncmpnext_line_80040d54, strncmpnext_line_80040d5c, strncmpnext_line_80040d60,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    strncmpNextInput, wvalM, wentryM, widthOfM, name_lbu_value,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem strncmpNext_input {p q stop ra previous b c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpNextInput p q stop previous)) (nonzero : previous ≠ 0#8)
    (left : ReadWindow (p + 1#64) 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[(p + 1#64).toNat]?).getD 0 = b) (pinR : (c.σ.mem[q.toNat]?).getD 0 = b) :
    BlockInput strncmpNextBlocks 0x80040d54#64 (strncmpNextInput p q stop previous) [[b], [b]] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12, 15]; decide
  shape := by change ChainOK _ [10, 11, 12, 15] _; decide
  tick := leaf.tick
  facts := by
    have code := strncmpNext_code leaf.image
    chain_facts code with "Vsa.Sim.Code.strncmp_at_"
    · strncmp_next_nf
      exact beq_eq_false_iff_ne.mpr (fun eq => nonzero ((nameByteWord_zero previous).mp eq))
    · exact left.lbu rfl (BitVec.add_zero _) pinL
    · exact right.lbu rfl (BitVec.add_zero q) pinR
    · strncmp_next_nf
      simp only [guardB, bne_self_eq_false]

/-- Advance one byte of an equal nonzero bounded prefix. -/
theorem strncmp_next (c : Config) (p q stop ra : BitVec 64) (previous b : BitVec 8)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (strncmpNextInput p q stop previous))
    (nonzero : previous ≠ 0#8) (left : ReadWindow (p + 1#64) 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[(p + 1#64).toNat]?).getD 0 = b) (pinR : (c.σ.mem[q.toNat]?).getD 0 = b) :
    FnSummary 0x80040d54#64 (fun d => d = c)
      (WriteRegistersPost [10, 15, 14] [] c 0x80040d68#64 (p + 1#64) (strncmpNextRegs p q stop b)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpNext_input leaf regs nonzero left right pinL pinR))
  · rfl
  · rfl
  · change [(14, bytesVal .lbu [b]), (15, bytesVal .lbu [b]), (10, p + 1#64), (11, q), (12, stop)] = _
    rw [name_lbu_value]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
