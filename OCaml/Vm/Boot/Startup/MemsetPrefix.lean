import OCaml.Vm.Boot.Startup.MemsetPrefixNormalized
import OCaml.Vm.Boot.Startup.MemsetPrefixImage
import OCaml.Vm.Primitives.Boundary
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def memsetPrefixBlocks : List BBlock :=
  memsetX276cFSeg ++ memsetX2778FSeg ++ memsetX2780FSeg ++ memsetX2784Seg

def memsetPrefixInput (p : BitVec 64) : GRegs := [(10, p), (11, 0#64), (12, 56#64)]

def memsetPrefixRegs (p : BitVec 64) : GRegs :=
  [(13, 48#64 + p), (12, 8#64), (15, 0#64), (14, p), (6, 15#64), (10, p), (11, 0#64)]

theorem aligned_mask16 {p : BitVec 64} (aligned : p.toNat % 16 = 0) : p &&& 15#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2^4 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact aligned

structure Memset56Input (p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  pointer : gprGet c.σ 10 = some p
  zero : gprGet c.σ 11 = some 0#64
  size : gprGet c.σ 12 = some 56#64
  alignedPointer : p.toNat % 16 = 0

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

local macro "memset_prefix_nf" : tactic =>
  `(tactic| simp only [memsetprefix_line_8004276c, memsetprefix_line_80042770,
    memsetprefix_line_80042778, memsetprefix_line_80042784, memsetprefix_line_80042788,
    memsetprefix_line_8004278c, runGM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG,
    wvalM, imm20Of, memsetPrefixInput, Option.getD_some, zero_imm, BitVec.add_zero, Nat.reduceEqDiff, ite_true, ite_false])

theorem memsetPrefix_input {p ra : BitVec 64} {c : Config} (h : Memset56Input p ra c) :
    BlockInput memsetPrefixBlocks 0x8004276c#64 (memsetPrefixInput p) [] c where
  good := h.good
  minstret := h.minstret
  regs := ⟨h.pointer, h.zero, h.size, trivial⟩
  keys := by change KeysOK [10, 11, 12]; decide
  shape := by change ChainOK _ [10, 11, 12] _; decide
  tick := h.tick
  facts := by
    have code := memsetPrefix_code h.image
    have mask := aligned_mask16 h.alignedPointer
    change p &&& Functions.sign_extend (m := 64) 0x00f#12 = 0#64 at mask
    chain_facts code with "Vsa.Sim.Code.memset_at_"
    all_goals memset_prefix_nf
    all_goals try rw [mask]
    all_goals decide

theorem memsetPrefix_regs {p : BitVec 64} (aligned : p.toNat % 16 = 0) :
    (evalBlocks memsetPrefixBlocks (SegEvalState.init (memsetPrefixInput p) [])).regs = memsetPrefixRegs p := by
  have mask := aligned_mask16 aligned
  change p &&& Functions.sign_extend (m := 64) 0x00f#12 = 0#64 at mask
  simp only [memsetPrefixBlocks, memsetX276cFSeg, memsetX2778FSeg, memsetX2780FSeg, memsetX2784Seg,
    List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  memset_prefix_nf
  rw [mask]
  rfl

/-- The aligned 56-byte zeroing path enters the word loop with a 48-byte
limit and eight tail bytes, without changing memory. -/
theorem memset56_prefix (c : Config) (p ra : BitVec 64) (h : Memset56Input p ra c) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [6, 14, 15, 13, 12] c ra 0x80042790#64 (memsetPrefixRegs p)) := by
  apply boundary_of_blocks h.toLeafInput (block_summary _ _ _ _ _ (memsetPrefix_input h))
  · rfl
  · rfl
  · intro σ pins
    rw [memsetPrefix_regs h.alignedPointer] at pins
    exact pins
  · decide
  · decide
end OCaml.Vm.Boot.Startup
