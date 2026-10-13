import OCaml.Vm.Boot.Startup.OpenSteps
import OCaml.Vm.Boot.Startup.ChildScan
import OCaml.Vm.Boot.Startup.HtifOpenFlagsNormalized
import OCaml.Vm.Boot.Startup.HtifOpenFlagsImage
import OCaml.Vm.Boot.Startup.HtifOpenAccessNormalized
import OCaml.Vm.Boot.Startup.HtifOpenAccessImage
import OCaml.Vm.Boot.Startup.HtifOpenTruncNormalized
import OCaml.Vm.Boot.Startup.HtifOpenTruncImage
import OCaml.Vm.Boot.Startup.HtifOpenDirectoryNormalized
import OCaml.Vm.Boot.Startup.HtifOpenDirectoryImage
import OCaml.Vm.Boot.Startup.HtifOpenCreatNormalized
import OCaml.Vm.Boot.Startup.HtifOpenCreatImage
import OCaml.Vm.Boot.Startup.HtifOpenScanNormalized
import OCaml.Vm.Boot.Startup.HtifOpenScanImage
import OCaml.Vm.Boot.Startup.HtifOpenSlotNormalized
import OCaml.Vm.Boot.Startup.HtifOpenSlotImage
import OCaml.Vm.Boot.Startup.HtifOpenNextNormalized
import OCaml.Vm.Boot.Startup.HtifOpenNextImage
import OCaml.Vm.Boot.Startup.HtifOpenNodeNormalized
import OCaml.Vm.Boot.Startup.HtifOpenNodeImage
import OCaml.Vm.Boot.Startup.HtifOpenStoreNormalized
import OCaml.Vm.Boot.Startup.HtifOpenStoreImage
import OCaml.Vm.Boot.Startup.HtifOpenStoresNormalized
import OCaml.Vm.Boot.Startup.HtifOpenStoresImage
import OCaml.Vm.Boot.Startup.HtifOpenRestoreNormalized
import OCaml.Vm.Boot.Startup.HtifOpenRestoreImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

/-! htif.c's `_open(path, O_RDONLY, ·)` when `resolve` finds a file: the
flag checks pass, the first free descriptor is taken. -/

open Sail in
/-- `auipc s2; addi s2,s2,1080` at 0x80000960: the `fds` table. -/
theorem open_fds_auipc : 2147486048#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 411927#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1080#12 = BitVec.ofNat 64 Layout.sym_fds := by decide

/-- After `resolve`: `R_FILE`, no `O_CREAT`, `O_TRUNC` or `O_DIRECTORY`: scan the descriptors. -/
theorem htif_open_file_front (c : Config) (sp a0 : BitVec 64) (ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ [(2, nativeStack sp 80), (8, 0#64), (9, 2#64), (18, 0#64), (10, a0)])
    (kind : read4 c.σ.mem (resAt sp 0) = [1#8, 0#8, 0#8, 0#8])
    (slashWord : read4 c.σ.mem (resAt sp 36) = [0#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x800008fc#64 (fun e => e = c) (WriteRegistersPost [9, 14, 15, 13, 11, 12, 18] [] c 0x80000980#64 a0
      [(12, 32#64), (9, 0#64), (14, BitVec.ofNat 64 Layout.sym_fds), (18, BitVec.ofNat 64 Layout.sym_fds), (13, 0#64),
        (15, 0#64), (11, 1#64), (2, nativeStack sp 80), (8, 0#64), (10, a0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (openX08fcFSeg ++ openX0908FSeg ++ openX091cTSeg ++ openX0a0cFSeg ++
        openX0a10TSeg ++ openX0a20TSeg ++ openX0a2cTSeg ++ openX0960Seg) 0x800008fc#64
        [(2, nativeStack sp 80), (8, 0#64), (9, 2#64), (18, 0#64), (10, a0)]
        [[1#8, 0#8, 0#8, 0#8], [0#8, 0#8, 0#8, 0#8]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 9, 18, 10]; decide
      shape := by change ChainOK _ [2, 8, 9, 18, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenKind_code leaf.image
        have word (off : Nat) (bound : off + 4 ≤ 80) (aligned : off % 4 = 0) :
            ReadWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 4 := by
          have w : WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 4 := by
            rw [nativeStack, frame.address _ (by omega)]
            exact frame.word32 bound aligned
          exact w.read
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (word 0 (by decide) (by decide)).lw rfl rfl (by rw [← kind]; exact read4_pins _ _)
        · simp only [htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopentrunc_line_80000a10, htifopentrunc_line_80000a14, htifopenscan_line_80000960, htifopenscan_line_80000964, htifopenscan_line_80000968, htifopenscan_line_8000096c, htifopenscan_line_80000970, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons]
          decide
        · refine memFacts_writeLog ((word 36 (by decide) (by decide)).lw rfl rfl
            (by rw [← slashWord]; exact read4_pins _ _)) (fun _ => by simp only [htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopentrunc_line_80000a10, htifopentrunc_line_80000a14, htifopenscan_line_80000960, htifopenscan_line_80000964, htifopenscan_line_80000968, htifopenscan_line_8000096c, htifopenscan_line_80000970, wlogM]; trivial)
        all_goals (simp only [htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopentrunc_line_80000a10, htifopentrunc_line_80000a14, htifopenscan_line_80000960, htifopenscan_line_80000964, htifopenscan_line_80000968, htifopenscan_line_8000096c, htifopenscan_line_80000970, runGM, stepGM, srcVal, lookupG, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons]; decide) }))
  · rfl
  · rfl
  · simp only [openX08fcFSeg, openX0908FSeg, openX091cTSeg, openX0a0cFSeg, openX0a10TSeg, openX0a20TSeg, openX0a2cTSeg,
      openX0960Seg, evalBlocks, evalBlock, SegEvalState.init, htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopentrunc_line_80000a10, htifopentrunc_line_80000a14, htifopenscan_line_80000960, htifopenscan_line_80000964, htifopenscan_line_80000968, htifopenscan_line_8000096c, htifopenscan_line_80000970, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal,
      lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff,
      ite_true, ite_false, imm20Of, List.cons_append, List.nil_append]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    refine ⟨by decide, by decide, ?_, open_fds_auipc, by decide, by decide, by decide⟩
    rw [open_fds_auipc, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · decide

def fdSlot (i : Nat) : BitVec 64 := BitVec.ofNat 64 (Layout.sym_fds + 24 * i)

theorem fdSlot_nat {i : Nat} (small : i ≤ 32) : (fdSlot i).toNat = Layout.sym_fds + 24 * i := by
  unfold fdSlot; rw [BitVec.toNat_ofNat]; unfold Layout.sym_fds; omega

theorem fdSlot_window {i : Nat} (small : i < 32) : ReadWindow (fdSlot i) 4 := by
  have h := fdSlot_nat (i := i) (by omega)
  refine ⟨?_, ?_, Or.inr ?_⟩ <;> rw [h] <;> simp only [Layout.sym_fds, Layout.sym_tohost] <;> omega

theorem fdSlot_next (i : Nat) : fdSlot i + Functions.sign_extend (m := 64) 24#12 = fdSlot (i + 1) := by
  unfold fdSlot
  rw [show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide, show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl,
    ← BitVec.ofNat_add]
  congr 1

/-- Descriptor `i` is taken: try `i + 1`. -/
theorem htif_open_slot_busy (c : Config) (ra a0 : BitVec 64) (i : Nat) (k : List (BitVec 8)) (leaf : LeafInput ra c)
    (small : i + 1 < 32) (regs : GHolds c.σ [(14, fdSlot i), (9, BitVec.ofNat 64 i), (12, 32#64), (10, a0)])
    (word : read4 c.σ.mem (Layout.sym_fds + 24 * i) = k) (busy : bytesVal .lw k ≠ 0#64) :
    FnSummary 0x80000980#64 (fun e => e = c) (WriteRegistersPost [13, 14, 9] [] c 0x80000980#64 a0
      [(9, BitVec.ofNat 64 (i + 1)), (14, fdSlot (i + 1)), (13, bytesVal .lw k), (12, 32#64), (10, a0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (openX0980TSeg ++ openX0978FSeg) 0x80000980#64
        [(14, fdSlot i), (9, BitVec.ofNat 64 i), (12, 32#64), (10, a0)] [k] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 9, 12, 10]; decide
      shape := by change ChainOK _ [14, 9, 12, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenSlot_code leaf.image
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (fdSlot_window (by omega)).lw rfl (BitVec.add_zero _)
            (by rw [fdSlot_nat (by omega), ← word]; exact read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw k) 0#64 = true
          exact bne_iff_ne.mpr busy
        · change guardB bop.BEQ (Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb
            (BitVec.ofNat 64 i + Functions.sign_extend (m := 64) 1#12) 31 0)) 32#64 = false
          rw [addiw_one i (by omega)]
          refine beq_eq_false_iff_ne.mpr fun e => ?_
          have := congrArg BitVec.toNat e
          simp only [BitVec.toNat_ofNat] at this
          omega }))
  · rfl
  · rfl
  · simp only [openX0980TSeg, openX0978FSeg, evalBlocks, evalBlock, SegEvalState.init, htifopenslot_line_80000980,
      htifopenslot_line_80000984, htifopennext_line_80000978, runGM, ldsRunM, wlogM, stepGM, stepLdsM, srcVal, lookupG,
      eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true,
      ite_false, List.cons_append, List.nil_append]
    rw [addiw_one i (by omega), fdSlot_next]
  · rfl
  · decide

/-- `opens + 1` as `addiw` computes it. -/
def opensNext (w : List (BitVec 8)) : BitVec 64 :=
  Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (bytesVal .lw w + Functions.sign_extend (m := 64) 1#12) 31 0)

/-- Descriptor 3 is free: select `r.node` and read its open count. -/
theorem htif_open_take (c : Config) (sp ra a0 : BitVec 64) (opens : List (BitVec 8)) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80)
    (regs : GHolds c.σ [(14, fdSlot 3), (9, 3#64), (12, 32#64), (10, a0), (11, 1#64),
      (2, nativeStack sp 80), (8, 0#64), (18, BitVec.ofNat 64 Layout.sym_fds)])
    (free : read4 c.σ.mem (Layout.sym_fds + 24 * 3) = [0#8, 0#8, 0#8, 0#8])
    (dir : List (BitVec 8)) (dirWord : read4 c.σ.mem (resAt sp 4) = dir)
    (node : read4 c.σ.mem (resAt sp 8) = [1#8, 0#8, 0#8, 0#8])
    (opensWord : read4 c.σ.mem (Layout.sym_files + 56 + 48) = opens) :
    FnSummary 0x80000980#64 (fun e => e = c)
      (WriteRegistersPost [13, 14, 10, 12, 11] [] c 0x800009dc#64 1#64
        [(11, 4#64), (12, opensNext opens), (14, BitVec.ofNat 64 (Layout.sym_fds + 72)),
          (13, BitVec.ofNat 64 (Layout.sym_files + 56)), (10, 1#64), (9, 3#64), (2, nativeStack sp 80), (8, 0#64),
          (18, BitVec.ofNat 64 Layout.sym_fds)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (openX0980FSeg ++ openX098cFSeg ++ openX0994FSeg ++ openX099cSeg ++
        openX09a0FSeg ++ openX09a8Seg) 0x80000980#64
        [(14, fdSlot 3), (9, 3#64), (12, 32#64), (10, a0), (11, 1#64), (2, nativeStack sp 80), (8, 0#64),
          (18, BitVec.ofNat 64 Layout.sym_fds)]
        [[0#8, 0#8, 0#8, 0#8], dir, [1#8, 0#8, 0#8, 0#8], opens] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 9, 12, 10, 11, 2, 8, 18]; decide
      shape := by change ChainOK _ [14, 9, 12, 10, 11, 2, 8, 18] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenSlot_code leaf.image
        have word (off : Nat) (bound : off + 4 ≤ 80) (aligned : off % 4 = 0) :
            ReadWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 4 := by
          have w : WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 4 := by
            rw [nativeStack, frame.address _ (by omega)]
            exact frame.word32 bound aligned
          exact w.read
        have opensWin : ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 56 + 48)) 4 := by constructor <;> decide
        have opensNat : (BitVec.ofNat 64 (Layout.sym_files + 56 + 48)).toNat = Layout.sym_files + 56 + 48 := by decide
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (fdSlot_window (i := 3) (by decide)).lw rfl (BitVec.add_zero _)
            (by rw [fdSlot_nat (i := 3) (by decide), ← free]; exact read4_pins _ _)
        · change guardB bop.BNE (bytesVal .lw [0#8, 0#8, 0#8, 0#8]) 0#64 = false
          decide
        · refine memFacts_writeLog ((word 4 (by decide) (by decide)).lw rfl rfl
            (by rw [← dirWord]; exact read4_pins _ _)) (fun _ => by simp only [htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]; simp only [wlogM]; trivial)
        · change guardB bop.BEQ 1#64 0#64 = false
          decide
        · simp only [htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]
          decide
        · refine memFacts_writeLog ((word 8 (by decide) (by decide)).lw rfl rfl
            (by rw [← node]; exact read4_pins _ _)) (fun _ => by simp only [htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]; simp only [wlogM]; trivial)
        · simp only [htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]
          decide
        · refine memFacts_writeLog (opensWin.lw rfl ?_ ?_) (fun _ => ?_)
          · simp only [ldsRunM, stepLdsM, List.headD_cons, List.tail_cons, htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]
            decide
          · rw [opensNat, ← opensWord]; exact read4_pins _ _
          · simp only [htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of]; simp only [wlogM]; trivial
        }))
  · rfl
  · rfl
  · simp only [openX0980FSeg, openX098cFSeg, openX0994FSeg, openX099cSeg, openX09a0FSeg, openX09a8Seg, evalBlocks,
      evalBlock, SegEvalState.init, htifopenslot_line_80000980, htifopenslot_line_80000984, htifopennode_line_8000098c, htifopennode_line_80000994, htifopennode_line_8000099c, htifopennode_line_800009a0, htifopenstore_line_800009a8, htifopenstore_line_800009ac, htifopenstore_line_800009b0, htifopenstore_line_800009b4, htifopenstore_line_800009b8, htifopenstore_line_800009bc, htifopenstore_line_800009c0, htifopenstore_line_800009c4, htifopenstore_line_800009c8, htifopenstore_line_800009cc, htifopenstore_line_800009d0, htifopenstore_line_800009d4, htifopenstore_line_800009d8, runGM, ldsRunM, wlogM, stepGM, stepLdsM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      imm20Of, List.cons_append, List.nil_append]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by decide, rfl, by decide, by decide, by decide⟩
  · rfl
  · decide

/-- `fds[3]`'s fields and the file's open count. -/
def htifOpenTakeLog (opens : BitVec 64) : List WEntry :=
  [(Layout.sym_files + 56 + 48, 4, opens), (Layout.sym_fds + 72 + 4, 4, 1#64), (Layout.sym_fds + 72 + 8, 8, 0#64),
    (Layout.sym_fds + 72 + 16, 4, 0#64), (Layout.sym_fds + 72, 4, 4#64)]

/-- `files[1].opens++`; `fds[3] = {FD_FILE, 1, 0, 0}`. -/
theorem htif_open_stores (c : Config) (ra opens : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(13, BitVec.ofNat 64 (Layout.sym_files + 56)), (12, opens),
      (14, BitVec.ofNat 64 (Layout.sym_fds + 72)), (10, 1#64), (8, 0#64), (11, 4#64)]) :
    FnSummary 0x800009dc#64 (fun e => e = c) (WriteRegistersPost [] (htifOpenTakeLog opens) c 0x800009f0#64 1#64
      [(13, BitVec.ofNat 64 (Layout.sym_files + 56)), (12, opens), (14, BitVec.ofNat 64 (Layout.sym_fds + 72)),
        (10, 1#64), (8, 0#64), (11, 4#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [htifOpenTakeLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput openX09dcSeg 0x800009dc#64
        [(13, BitVec.ofNat 64 (Layout.sym_files + 56)), (12, opens), (14, BitVec.ofNat 64 (Layout.sym_fds + 72)),
          (10, 1#64), (8, 0#64), (11, 4#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [13, 12, 14, 10, 8, 11]; decide
      shape := by change ChainOK _ [13, 12, 14, 10, 8, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenStores_code leaf.image
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_files + 56 + 48)) 4 by constructor <;> decide).sw rfl
            (by simp only [htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 72 + 4)) 4 by constructor <;> decide).sw rfl
            (by simp only [htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 72 + 8)) 8 by constructor <;> decide).sd rfl
            (by simp only [htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 72 + 16)) 4 by constructor <;> decide).sw rfl
            (by simp only [htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide)
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 72)) 4 by constructor <;> decide).sw rfl
            (by simp only [htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff]; decide) }))
  · simp only [openX09dcSeg, evalBlocks, evalBlock, SegEvalState.init, htifopenstores_line_800009dc, htifopenstores_line_800009e0, htifopenstores_line_800009e4, htifopenstores_line_800009e8, htifopenstores_line_800009ec, runGM, ldsRunM, wlogM, stepGM, stepLdsM,
      eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some,
      Nat.reduceEqDiff, ite_true, ite_false, List.cons_append, List.nil_append, htifOpenTakeLog]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by decide, by decide, by decide, by decide, by decide⟩
  · rfl
  · rfl
  · rfl
  · decide

/-- Restore `_open`'s saves and return the descriptor. -/
theorem htif_open_succeed (c : Config) (sp ra s0 s1 s2 fd oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ [(9, fd), (2, nativeStack sp 80)])
    (saved : ∀ off value, (off, value) ∈ [(64, s0), (72, ra), (48, s2), (56, s1)] →
      bytesT c.σ.mem (nativeFrameBase sp 80 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800009f0#64 (fun e => e = c) (WriteRegistersPost [2, 9, 10, 18, 1, 8] [] c ra fd
      [(2, sp), (9, s1), (10, fd), (18, s2), (1, ra), (8, s0)]) := by
  have savedRa := saved 72 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (openX09f0Seg ++ openX09f4Seg) 0x800009f0#64
        [(9, fd), (2, nativeStack sp 80)] (htifOpenRestoreLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [9, 2]; decide
      shape := by change ChainOK _ [9, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenRestore_code leaf.image
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (frame.read_slot (off := 64) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 72) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [openX09f0Seg, openX09f4Seg, evalBlocks, evalBlock, SegEvalState.init, htifopenrestore_line_800009f0, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, htifOpenRestoreLoads, List.map_cons,
      List.map_nil, read8_value, List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 80#12 = 80#64 by decide, nativeStack_restore, open_se0, BitVec.add_zero,
      saved 56 s1 (by simp), saved 48 s2 (by simp), savedRa, saved 64 s0 (by simp)]
  · rfl
  · decide

/-- `_open` succeeded: return its descriptor. -/
theorem open_r_succeed (c : Config) (sp ra s0 fd oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ [(10, fd), (2, nativeStack sp 16)]) (ok : fd ≠ -1#64)
    (saved : ∀ off value, (off, value) ∈ [(8, ra), (0, s0)] →
      bytesT c.σ.mem (nativeFrameBase sp 16 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8004d7d0#64 (fun e => e = c)
      (WriteRegistersPost [2, 8, 1, 15] [] c ra fd [(2, sp), (8, s0), (1, ra), (15, -1#64), (10, fd)]) := by
  have savedRa := saved 8 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (open_rXd7d0FSeg ++ open_rXd7d8Seg) 0x8004d7d0#64
        [(10, fd), (2, nativeStack sp 16)]
        [read8 c.σ.mem (nativeFrameBase sp 16 + 8), read8 c.σ.mem (nativeFrameBase sp 16 + 0)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := openRCheck_code leaf.image
        chain_facts code with "Vsa.Sim.Code._open_r_at_"
        · change guardB bop.BEQ fd (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
          rw [show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
          exact beq_eq_false_iff_ne.mpr ok
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [open_rXd7d0FSeg, open_rXd7d8Seg, evalBlocks, evalBlock, SegEvalState.init, openrcheck_line_8004d7d0,
      openrreturn_line_8004d7d8, openrreturn_line_8004d7dc, openrreturn_line_8004d7e0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, read8_value,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, nativeStack_restore, savedRa,
      saved 0 s0 (by simp), show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
