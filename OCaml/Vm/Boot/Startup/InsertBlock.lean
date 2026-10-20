import OCaml.Vm.Boot.Startup.BibEntryNormalized
import OCaml.Vm.Boot.Startup.BibEntryImage
import OCaml.Vm.Boot.Startup.BibLeastNormalized
import OCaml.Vm.Boot.Startup.BibLeastImage
import OCaml.Vm.Boot.Startup.BibRootNormalized
import OCaml.Vm.Boot.Startup.BibRootImage
import OCaml.Vm.Boot.Startup.InitMerge
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! bf_insert_block into an empty best-fit tree with no least block: the block
becomes the root, its own sibling ring, without children. -/

/-- `bf_large_tree`. -/
def largeTreeAddr : Nat := 0x800649f8
/-- `bf_large_least`. -/
def largeLeastAddr : Nat := 0x800649f0

/-- The block's tree node: no children, its own ring, then the root pointer. -/
def rootLog (b : BitVec 64) : List WEntry :=
  [((b + 16#64).toNat, 8, 0#64), ((b + 8#64).toNat, 8, 0#64), ((b + 32#64).toNat, 8, b), ((b + 24#64).toNat, 8, b),
    (b.toNat, 4, 1#64), (largeTreeAddr, 8, b)]

theorem srli_ten (x : BitVec 64) (a : MInstr) (imm : a.imm = 10#12) :
    Sail.shift_bits_right x (Sail.BitVec.extractLsb (shamtOf a) 5 0) = x >>> 10 := by
  rw [shamtOf, imm]
  simp only [Sail.shift_bits_right, BitVec.ushiftRight_eq']
  rfl

local macro "bfk" : tactic => `(tactic| simp only [bibentry_line_80005e10, bibentry_line_80005e14, bibentry_line_80005e18, bibentry_line_80005e1c, bibentry_line_80005e20, bibentry_line_80005e24, bibentry_line_80005e28, bibleast_line_80005fe0, bibleast_line_80005fe4, bibleast_line_80005fec, bibleast_line_80005ff0, bibleast_line_80005ff4, bibleast_line_80005ff8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])
local macro "brk" : tactic => `(tactic| simp only [bibroot_line_80005f84, bibroot_line_80005f88, bibroot_line_80005f8c, bibroot_line_80005f90, bibroot_line_80005f94, bibroot_line_80005f98, bibroot_line_80005f9c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff])

def bibFindBlocks : List BBlock :=
  bf_insert_blockX5e10FSeg ++ bf_insert_blockX5e30Seg ++ bf_insert_blockX5fdcTSeg ++ bf_insert_blockX5ff4Seg

/-- Read the header, the empty tree and the absent least block. -/
theorem bib_find (c : Config) (ra b hd : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, b), (1, ra)])
    (headerWindow : ReadWindow (b - 8#64) 8) (header : bytesT c.σ.mem (b - 8#64).toNat 8 = hd)
    (tree : bytesT c.σ.mem largeTreeAddr 8 = 0#64) (least : bytesT c.σ.mem largeLeastAddr 8 = 0#64) :
    FnSummary 0x80005e10#64 (fun e => e = c) (WriteRegistersPost [16, 14, 13, 11, 12] [] c 0x80005f84#64 b
      [(16, 0x800649f8#64), (14, hd >>> 10), (13, 0#64), (11, 0#64), (12, 0x800649f8#64), (10, b), (1, ra)]) := by
  have hdr : bytesVal .ld (read8 c.σ.mem (b - 8#64).toNat) = hd := by rw [read8_value]; exact header
  have root : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 largeTreeAddr).toNat) = 0#64 := by rw [read8_value]; exact tree
  have least0 : bytesVal .ld (read8 c.σ.mem (BitVec.ofNat 64 largeLeastAddr).toNat) = 0#64 := by
    rw [read8_value]; exact least
  apply registers_of_blocks' leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput bibFindBlocks 0x80005e10#64 [(10, b), (1, ra)]
        [read8 c.σ.mem (b - 8#64).toNat, read8 c.σ.mem (BitVec.ofNat 64 largeTreeAddr).toNat,
          read8 c.σ.mem (BitVec.ofNat 64 largeLeastAddr).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 1]; decide
      shape := by change ChainOK _ [10, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := bibEntry_code leaf.image
        unfold bibFindBlocks
        chain_facts code with "Vsa.Sim.Code.bf_insert_block_at_"
        · exact headerWindow.ld rfl (by bfk; rw [show Functions.sign_extend (m := 64) 0xff8#12 = -8#64 by decide,
            ← BitVec.sub_eq_add_neg]) (read8_pins _ _)
        · exact (show ReadWindow (BitVec.ofNat 64 largeTreeAddr) 8 by constructor <;> decide).ld rfl (by bfk; decide)
            (read8_pins _ _)
        · exact (show ReadWindow (BitVec.ofNat 64 largeLeastAddr) 8 by constructor <;> decide).ld rfl (by bfk; decide)
            (read8_pins _ _)
        · bfk; rw [root]; rfl
        · bfk; rw [least0]; rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [bibFindBlocks, bf_insert_blockX5e10FSeg, bf_insert_blockX5e30Seg, bf_insert_blockX5fdcTSeg,
      bf_insert_blockX5ff4Seg, List.cons_append, List.nil_append, evalBlocks, evalBlock, SegEvalState.init, runGM,
      stepGM, stepLdsM, ldsRunM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.headD_cons, List.tail_cons, imm20Of, bibentry_line_80005e10, bibentry_line_80005e14, bibentry_line_80005e18, bibentry_line_80005e1c, bibentry_line_80005e20, bibentry_line_80005e24, bibentry_line_80005e28, bibleast_line_80005fe0, bibleast_line_80005fe4, bibleast_line_80005fec, bibleast_line_80005ff0, bibleast_line_80005ff4, bibleast_line_80005ff8] at pins
    rw [hdr, srli_ten _ _ rfl] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 14) _ pins rfl,
      gholds_lookup_eq pins rfl root, gholds_lookup_eq pins rfl least0, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 1) _ pins rfl, trivial⟩
  · rfl
  · decide

/-- Make the block the root; return. -/
theorem bib_root (c : Config) (ra b : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, b), (12, 0x800649f8#64), (1, ra)])
    (window : ∀ off, off + 8 ≤ 40 → off % 8 = 0 → WriteWindow (b + BitVec.ofNat 64 off) 8)
    (window4 : WriteWindow b 4) (outside : ImageOutside (rootLog b)) :
    FnSummary 0x80005f84#64 (fun e => e = c) (WriteRegistersPost [15] (rootLog b) c ra b
      [(15, 1#64), (10, b), (12, 0x800649f8#64), (1, ra)]) := by
  apply registers_of_blocks' leaf.image outside
    (block_summary _ _ _ _ _ (show BlockInput bf_insert_blockX5f84Seg 0x80005f84#64
        [(10, b), (12, 0x800649f8#64), (1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 12, 1]; decide
      shape := by change ChainOK _ [10, 12, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := bibRoot_code leaf.image
        chain_facts code with "Vsa.Sim.Code.bf_insert_block_at_"
        · exact (window 16 (by decide) (by decide)).sd rfl (by brk; rw [show Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 by decide])
        · exact (window 8 (by decide) (by decide)).sd rfl (by brk; rw [show Functions.sign_extend (m := 64) 8#12 = BitVec.ofNat 64 8 by decide])
        · exact (window 32 (by decide) (by decide)).sd rfl (by brk; rw [show Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 by decide])
        · exact (window 24 (by decide) (by decide)).sd rfl (by brk; rw [show Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 by decide])
        · exact window4.sw rfl (by brk; rw [sext_zero, BitVec.add_zero])
        · exact (show WriteWindow (BitVec.ofNat 64 largeTreeAddr) 8 by constructor <;> decide).sd rfl
            (by brk; rw [sext_zero, BitVec.add_zero]; rfl)
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · simp only [bf_insert_blockX5f84Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, wlogM, wentryM, widthOfM,
      eaddrM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, bibroot_line_80005f84, bibroot_line_80005f88, bibroot_line_80005f8c, bibroot_line_80005f90, bibroot_line_80005f94, bibroot_line_80005f98, bibroot_line_80005f9c]
    rw [sext_zero, BitVec.add_zero, show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide,
      show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide, show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide,
      show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide, show 0#64 + Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
    rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [ret_tgt ra leaf.aligned]
  · intro σ pins
    simp only [bf_insert_blockX5f84Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG, eraseG,
      wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, bibroot_line_80005f84, bibroot_line_80005f88, bibroot_line_80005f8c, bibroot_line_80005f90, bibroot_line_80005f94, bibroot_line_80005f98, bibroot_line_80005f9c] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl, gholds_lookup (n := 12) _ pins rfl,
      gholds_lookup (n := 1) _ pins rfl, trivial⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
