import OCaml.Vm.Boot.Startup.AtomSaveNormalized
import OCaml.Vm.Boot.Startup.AtomSaveImage
import OCaml.Vm.Boot.Startup.AtomSaveCallInterface
import OCaml.Vm.Boot.Startup.AtomPublishNormalized
import OCaml.Vm.Boot.Startup.AtomPublishImage
import OCaml.Vm.Boot.Startup.AtomLoopNormalized
import OCaml.Vm.Boot.Startup.AtomLoopImage
import OCaml.Vm.Boot.Startup.MinorRefSteps
import OCaml.Vm.Boot.Startup.InitStackSteps
import OCaml.Vm.Boot.Startup.BlockCall
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! caml_init_atom_table's blocks. -/

/-- `caml_atom_table`. -/
def atomTableAddr : Nat := 0x800649a0

def atomSaveLog (sp ra : BitVec 64) : List WEntry := nativeWordLog sp 32 [(24, ra)]

/-- Open a 32-byte frame, save ra; `caml_stat_alloc_aligned_noexc(Page_size, 0, &b)`
with `b` at `8(sp)`. -/
theorem atom_save (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(2, sp), (1, ra)]) :
    FnSummary 0x800044a4#64 (fun e => e = c) (WriteRegistersPost [2, 12, 11, 10] (atomSaveLog sp ra) c
      jal_800044b8_call.pc 0x1000#64
      [(2, nativeStack sp 32), (12, nativeStack sp 32 + 8#64), (11, 0#64), (10, 0x1000#64)]) := by
  have inside : LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (atomSaveLog sp ra) :=
    frame.word_log_inside fun off value member => by simp at member; omega
  apply registers_of_blocks' leaf.image (frame.image_outside inside)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_atom_tableX44a4Seg 0x800044a4#64
        [(2, sp), (1, ra)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1]; decide
      shape := by change ChainOK _ [2, 1] _; decide
      tick := leaf.tick
      facts := by
        have code := atomSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_init_atom_table_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · intro σ pins
    simp only [caml_init_atom_tableX44a4Seg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, srcVal, lookupG,
      eraseG, wvalM, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, atomsave_line_800044a4,
      atomsave_line_800044a8, atomsave_line_800044ac, atomsave_line_800044b0, atomsave_line_800044b4] at pins
    exact ⟨gholds_lookup (n := 2) _ pins rfl, gholds_lookup_eq pins rfl rfl, gholds_lookup_eq pins rfl (by decide),
      gholds_lookup_eq pins rfl (by decide), trivial⟩
  · rfl
  · decide

theorem atom_save_call (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 32)
    (regs : GHolds c.σ [(2, sp), (1, ra)]) :
    FnSummary 0x800044a4#64 (fun e => e = c) (WriteRegistersPost ([2, 12, 11, 10] ++ [1]) (atomSaveLog sp ra) c
      jal_800044b8_call.target 0x1000#64 ((1, jal_800044b8_call.link) ::
      [(2, nativeStack sp 32), (12, nativeStack sp 32 + 8#64), (11, 0#64), (10, 0x1000#64)])) :=
  block_then_call c jal_800044b8_call_shape jal_800044b8_call_decode (fun _ h => jal_800044b8_call_pins h)
    (atom_save c sp ra leaf frame regs) (by simp only [keysG]; decide) (by simp only [KeysAvoidRa, keysG]; decide) rfl
local macro "apb" : tactic => `(tactic| simp only [atompublish_line_800044bc, atompublish_line_800044c0, atompublish_line_800044c4, atompublish_line_800044c8, atompublish_line_800044cc, atompublish_line_800044d0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
  Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, imm20Of, ldsRunM, stepLdsM, List.headD_cons,
  List.tail_cons])

/-- `caml_atom_table = b`; the loop's counter `a5 = 0`, header `a4 = Make_header(0, 0, Caml_black)`. -/
theorem atom_publish (c : Config) (ra base : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(10, base)]) :
    FnSummary 0x800044bc#64 (fun e => e = c) (WriteRegistersPost [12, 11, 14, 15] [(atomTableAddr, 8, base)] c
      0x800044d4#64 base
      [(12, BitVec.ofNat 64 atomTableAddr), (11, base), (14, 768#64), (15, 0#64), (10, base)]) := by
  apply registers_of_blocks' leaf.image (by constructor <;> simp only [OutLRange, atomTableAddr] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_atom_tableX44bcSeg 0x800044bc#64 [(10, base)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10]; decide
      shape := by change ChainOK _ [10] _; decide
      tick := leaf.tick
      facts := by
        have code := atomPublish_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_atom_table_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 atomTableAddr) 8 by constructor <;> decide).sd rfl
            (by apb; decide) }))
  · simp only [caml_init_atom_tableX44bcSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    apb
    refine congrArg (fun a => [(a, 8, base)]) ?_
    decide
  · rfl
  · intro σ pins
    simp only [caml_init_atom_tableX44bcSeg, evalBlocks, evalBlock, SegEvalState.init, atompublish_line_800044bc, atompublish_line_800044c0, atompublish_line_800044c4, atompublish_line_800044c8, atompublish_line_800044cc, atompublish_line_800044d0, runGM, stepGM, eraseG,
      wvalM, srcVal, lookupG, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, Option.getD_some] at pins
    exact ⟨gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by rw [sext_zero, BitVec.add_zero]),
      gholds_lookup_eq pins rfl (by decide), gholds_lookup_eq pins rfl (by decide), gholds_lookup (n := 10) _ pins rfl,
      trivial⟩
  · rfl
  · decide
theorem guard_bne_true {x : BitVec 64} (h : x ≠ 0#64) : guardB bop.BNE x 0#64 = true := by
  unfold guardB; simp [h]

theorem guard_bne_zero : guardB bop.BNE 0#64 0#64 = false := by decide

/-- The loop's cursor and header after `k` iterations. -/
abbrev atomCursor (k : Nat) : BitVec 64 := BitVec.ofNat 64 (8 * k)
abbrev atomHeader (k : Nat) : BitVec 64 := BitVec.ofNat 64 (768 + k)

theorem atom_cursor_next (k : Nat) : atomCursor k + Functions.sign_extend (m := 64) 8#12 = atomCursor (k + 1) := by
  rw [show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [atomCursor, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem atom_header_next (k : Nat) : atomHeader k + Functions.sign_extend (m := 64) 1#12 = atomHeader (k + 1) := by
  rw [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [atomHeader, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The loop's exit test `a5 - 2048` after the increment: nonzero before the last atom. -/
theorem atom_test_more (k : Nat) (hk : k + 1 < 256) :
    atomCursor k + Functions.sign_extend (m := 64) 8#12 + Functions.sign_extend (m := 64) 2048#12 ≠ 0#64 := by
  rw [atom_cursor_next, show Functions.sign_extend (m := 64) 2048#12 = 0xfffffffffffff800#64 by decide]
  intro h
  have e := congrArg (· + 2048#64) h
  simp only [BitVec.add_assoc, show (0xfffffffffffff800#64 + 2048#64 : BitVec 64) = 0#64 by decide,
    BitVec.add_zero, BitVec.zero_add] at e
  have v := congrArg BitVec.toNat e
  rw [atomCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), show (2048#64 : BitVec 64).toNat = 2048 by decide] at v
  omega

/-- … and zero after it. -/
theorem atom_test_last :
    atomCursor 255 + Functions.sign_extend (m := 64) 8#12 + Functions.sign_extend (m := 64) 2048#12 = 0#64 := by
  decide

/-- The atom words written so far. -/
def atomEntry (base : BitVec 64) (k : Nat) : WEntry := ((base + atomCursor k).toNat, 8, atomHeader k)

local macro "alp" : tactic => `(tactic| simp only [atomloop_line_800044d4, atomloop_line_800044d8, atomloop_line_800044dc, atomloop_line_800044e0, atomloop_line_800044e4, atomloop_line_800044e8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
  Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, Nat.reduceAdd, ldsRunM, stepLdsM, List.headD_cons,
  List.tail_cons])

/-- One iteration that loops back: atom `k`'s header, then `a1 = caml_atom_table`. -/
theorem atom_loop_more (c : Config) (ra base a0 : BitVec 64) (k : Nat) (hk : k + 1 < 256) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, base), (15, atomCursor k), (14, atomHeader k), (12, BitVec.ofNat 64 atomTableAddr),
      (10, a0)])
    (low : heapStart ≤ base.toNat) (high : base.toNat + 2048 ≤ heapEnd) (aligned : base.toNat % 8 = 0)
    (table : bytesT c.σ.mem atomTableAddr 8 = base) :
    FnSummary 0x800044d4#64 (fun e => e = c) (WriteRegistersPost [11, 15, 13, 14] [atomEntry base k] c 0x800044d4#64
      a0 [(11, base), (15, atomCursor (k + 1)), (14, atomHeader (k + 1)), (12, BitVec.ofNat 64 atomTableAddr),
        (10, a0)]) := by
  have hS : heapStart = 0x8007d140 := rfl
  have hE : heapEnd = 0x86800000 := rfl
  rw [hS] at low
  rw [hE] at high
  have addr : (base + atomCursor k).toNat = base.toNat + 8 * k := by
    rw [BitVec.toNat_add, atomCursor, BitVec.toNat_ofNat]
    simp only [Nat.reducePow]
    rw [Nat.mod_eq_of_lt (a := 8 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
  have window : WriteWindow (base + atomCursor k) 8 :=
    ⟨by rw [addr]; omega, by rw [addr]; omega, by rw [addr]; unfold Layout.sym_tohost; omega, by rw [addr]; omega⟩
  have word : bytesVal .ld (Primitives.read8 c.σ.mem (BitVec.ofNat 64 atomTableAddr).toNat) = base := by
    rw [read8_value]; exact table
  apply registers_of_blocks' leaf.image
    (by constructor <;> simp only [atomEntry, OutLRange, and_true] <;> rw [addr] <;>
      simp only [Image.textBase, Image.textSize, Image.rodataBase, Image.rodataSize] <;> omega)
    (block_summary _ _ _ _ _ (show BlockInput caml_init_atom_tableX44d4TSeg 0x800044d4#64
        [(11, base), (15, atomCursor k), (14, atomHeader k), (12, BitVec.ofNat 64 atomTableAddr), (10, a0)]
        [Primitives.read8 c.σ.mem (BitVec.ofNat 64 atomTableAddr).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 15, 14, 12, 10]; decide
      shape := by change ChainOK _ [11, 15, 14, 12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := atomLoop_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_init_atom_table_at_"
        · exact window.sd rfl (by alp; rw [sext_zero, BitVec.add_zero])
        · past_stores
          · exact (show ReadWindow (BitVec.ofNat 64 atomTableAddr) 8 by constructor <;> decide).ld rfl
              (by alp; rw [sext_zero, BitVec.add_zero]) (read8_pins _ _)
          all_goals (intro _; simp only [OutLRange, wentryM, widthOfM, and_true]; alp
                     simp only [sext_zero, BitVec.add_zero]
                     rw [addr, show (BitVec.ofNat 64 atomTableAddr).toNat = 0x800649a0 by decide]; omega)
        · alp
          exact guard_bne_true (atom_test_more k hk) }))
  · simp only [caml_init_atom_tableX44d4TSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM]
    alp
    simp only [sext_zero, BitVec.add_zero]
    rfl
  · simp only [evalBlocksPC, caml_init_atom_tableX44d4TSeg, SegEvalState.init, chainEndPC, endPCB, tgtPCT]
    decide
  · intro σ pins
    simp only [caml_init_atom_tableX44d4TSeg, evalBlocks, evalBlock, SegEvalState.init] at pins
    simp only [atomloop_line_800044d4, atomloop_line_800044d8, atomloop_line_800044dc, atomloop_line_800044e0,
      atomloop_line_800044e4, atomloop_line_800044e8, runGM, stepGM, eraseG, wvalM, srcVal, lookupG,
      ite_true, ite_false, Nat.reduceEqDiff, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons, Option.getD_some] at pins
    rw [word, atom_cursor_next, atom_header_next] at pins
    exact ⟨gholds_lookup (n := 11) _ pins rfl, gholds_lookup (n := 15) _ pins rfl, gholds_lookup (n := 14) _ pins rfl,
      gholds_lookup (n := 12) _ pins rfl, gholds_lookup (n := 10) _ pins rfl, trivial⟩
  · rfl
  · decide

end OCaml.Vm.Boot.Startup
