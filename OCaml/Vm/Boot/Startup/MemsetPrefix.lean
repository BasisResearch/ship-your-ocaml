import OCaml.Vm.Boot.Startup.MemsetPrefixNormalized
import OCaml.Vm.Boot.Startup.MemsetPrefixImage
import OCaml.Vm.Primitives.Boundary
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def memsetPrefixBlocks : List BBlock :=
  memsetX276cFSeg ++ memsetX2778FSeg ++ memsetX2780FSeg ++ memsetX2784Seg

def memsetPrefixInputN (p n : BitVec 64) : GRegs := [(10, p), (11, 0#64), (12, n)]

abbrev memsetPrefixInput (p : BitVec 64) : GRegs := memsetPrefixInputN p 56#64

/-- After the entry checks: the word loop's limit `p + (n & ~15)` and the
remainder `n & 15`. -/
def memsetPrefixRegsN (p n : BitVec 64) : GRegs :=
  [(13, (n &&& Functions.sign_extend (m := 64) 0xff0#12) + p), (12, n &&& Functions.sign_extend (m := 64) 0x00f#12),
    (15, 0#64), (14, p), (6, 15#64), (10, p), (11, 0#64)]

def memsetPrefixRegs (p : BitVec 64) : GRegs :=
  [(13, 48#64 + p), (12, 8#64), (15, 0#64), (14, p), (6, 15#64), (10, p), (11, 0#64)]

theorem aligned_mask16 {p : BitVec 64} (aligned : p.toNat % 16 = 0) : p &&& 15#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15#64).toNat = 2^4 - 1 from by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  exact aligned

/-- `memset(p, 0, n)` on a 16-aligned `p` with `n ≥ 16`. -/
structure MemsetInput (p n ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  pointer : gprGet c.σ 10 = some p
  zero : gprGet c.σ 11 = some 0#64
  size : gprGet c.σ 12 = some n
  alignedPointer : p.toNat % 16 = 0
  big : 16 ≤ n.toNat

structure Memset56Input (p ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  pointer : gprGet c.σ 10 = some p
  zero : gprGet c.σ 11 = some 0#64
  size : gprGet c.σ 12 = some 56#64
  alignedPointer : p.toNat % 16 = 0

theorem Memset56Input.general {p ra c} (h : Memset56Input p ra c) : MemsetInput p 56#64 ra c :=
  { h with big := by decide }

private theorem zero_imm : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

local macro "memset_prefix_nf" : tactic =>
  `(tactic| simp only [memsetprefix_line_8004276c, memsetprefix_line_80042770,
    memsetprefix_line_80042778, memsetprefix_line_80042784, memsetprefix_line_80042788,
    memsetprefix_line_8004278c, runGM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG,
    wvalM, imm20Of, memsetPrefixInputN, Option.getD_some, zero_imm, BitVec.add_zero, Nat.reduceEqDiff, ite_true, ite_false])

theorem memsetPrefix_inputN {p n ra : BitVec 64} {c : Config} (h : MemsetInput p n ra c) :
    BlockInput memsetPrefixBlocks 0x8004276c#64 (memsetPrefixInputN p n) [] c where
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
    have big : guardB bop.BGEU (0#64 + Functions.sign_extend (m := 64) 15#12) n = false := by
      have large := h.big
      rw [show 0#64 + Functions.sign_extend (m := 64) 15#12 = 15#64 by decide]
      unfold guardB Functions.zopz0zKzJ_u
      simp only [Sail.BitVec.toNatInt]
      exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_le.mp hc) (by simp only [BitVec.toNat_ofNat]; omega))
    chain_facts code with "Vsa.Sim.Code.memset_at_"
    all_goals memset_prefix_nf
    all_goals try rw [mask]
    all_goals first | exact big | decide

theorem memsetPrefix_input {p ra : BitVec 64} {c : Config} (h : Memset56Input p ra c) :
    BlockInput memsetPrefixBlocks 0x8004276c#64 (memsetPrefixInput p) [] c :=
  memsetPrefix_inputN h.general

theorem memsetPrefix_regsN {p n : BitVec 64} (aligned : p.toNat % 16 = 0) :
    (evalBlocks memsetPrefixBlocks (SegEvalState.init (memsetPrefixInputN p n) [])).regs = memsetPrefixRegsN p n := by
  have mask := aligned_mask16 aligned
  change p &&& Functions.sign_extend (m := 64) 0x00f#12 = 0#64 at mask
  simp only [memsetPrefixBlocks, memsetX276cFSeg, memsetX2778FSeg, memsetX2780FSeg, memsetX2784Seg,
    List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init]
  memset_prefix_nf
  rw [mask]
  rfl

theorem memsetPrefixRegs_eq (p : BitVec 64) : memsetPrefixRegsN p 56#64 = memsetPrefixRegs p := by
  simp only [memsetPrefixRegsN, memsetPrefixRegs]
  rw [show (56#64 &&& Functions.sign_extend (m := 64) 0xff0#12) = 48#64 by decide,
    show (56#64 &&& Functions.sign_extend (m := 64) 0x00f#12) = 8#64 by decide]

theorem memsetPrefix_regs {p : BitVec 64} (aligned : p.toNat % 16 = 0) :
    (evalBlocks memsetPrefixBlocks (SegEvalState.init (memsetPrefixInput p) [])).regs = memsetPrefixRegs p := by
  rw [memsetPrefix_regsN aligned, memsetPrefixRegs_eq]

/-- memset's entry checks on an aligned `p` and `n ≥ 16` lead into the word
loop without changing memory. -/
theorem memset_prefix (c : Config) (p n ra : BitVec 64) (h : MemsetInput p n ra c) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [6, 14, 15, 13, 12] c ra 0x80042790#64 (memsetPrefixRegsN p n)) := by
  apply boundary_of_blocks h.toLeafInput (block_summary _ _ _ _ _ (memsetPrefix_inputN h))
  · rfl
  · rfl
  · intro σ pins
    rw [memsetPrefix_regsN h.alignedPointer] at pins
    exact pins
  · decide
  · decide

/-- The aligned 56-byte zeroing path enters the word loop with a 48-byte
limit and eight tail bytes, without changing memory. -/
theorem memset56_prefix (c : Config) (p ra : BitVec 64) (h : Memset56Input p ra c) :
    FnSummary 0x8004276c#64 (fun d => d = c)
      (BoundaryPost [6, 14, 15, 13, 12] c ra 0x80042790#64 (memsetPrefixRegs p)) := by
  rw [← memsetPrefixRegs_eq]
  exact memset_prefix c p 56#64 ra h.general
end OCaml.Vm.Boot.Startup
