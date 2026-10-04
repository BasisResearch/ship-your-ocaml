import OCaml.Vm.Boot.Startup.StrncmpFirstNormalized
import OCaml.Vm.Boot.Startup.StrncmpFirstImage
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def strncmpFirstInput (p q n : BitVec 64) : GRegs := [(10, p), (11, q), (12, n)]
def strncmpEnd (p n : BitVec 64) : BitVec 64 := p + (n + (-1#64))
def strncmpFirstRegs (p q n : BitVec 64) (b : BitVec 8) : GRegs :=
  [(12, strncmpEnd p n), (14, nameByteWord b), (15, nameByteWord b), (10, p), (11, q)]

local macro "strncmp_first_nf" : tactic =>
  `(tactic| simp only [strncmpfirst_line_80040d3c, strncmpfirst_line_80040d40,
    strncmpfirst_line_80040d44, strncmpfirst_line_80040d48,
    runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM, eaddrM, srcVal, lookupG, eraseG,
    strncmpFirstInput, wvalM, wentryM, widthOfM, name_lbu_value,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem strncmpFirst_input {p q n ra b c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q n)) (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = b) (pinR : (c.σ.mem[q.toNat]?).getD 0 = b) :
    BlockInput strncmpX0d3cTSeg 0x80040d3c#64 (strncmpFirstInput p q n) [[b], [b]] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12]; decide
  shape := by change ChainOK _ [10, 11, 12] _; decide
  tick := leaf.tick
  facts := by
    have code := strncmpFirst_code leaf.image
    chain_facts code with "Vsa.Sim.Code.strncmp_at_"
    · exact left.lbu rfl (BitVec.add_zero p) pinL
    · exact right.lbu rfl (BitVec.add_zero q) pinR
    · strncmp_first_nf
      exact beq_self_eq_true _

/-- Equal first bytes select strncmp's bounded byte loop and compute its end pointer. -/
theorem strncmp_first (c : Config) (p q n ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (strncmpFirstInput p q n)) (left : ReadWindow p 1) (right : ReadWindow q 1)
    (pinL : (c.σ.mem[p.toNat]?).getD 0 = b) (pinR : (c.σ.mem[q.toNat]?).getD 0 = b) :
    FnSummary 0x80040d3c#64 (fun d => d = c)
      (WriteRegistersPost [15, 14, 12] [] c 0x80040d68#64 p (strncmpFirstRegs p q n b)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (strncmpFirst_input leaf regs left right pinL pinR))
  · rfl
  · rfl
  · change [(12, p + (n + (-1#64))), (14, bytesVal .lbu [b]), (15, bytesVal .lbu [b]), (10, p), (11, q)] = _
    rw [name_lbu_value]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
