import OCaml.Vm.Boot.Startup.OpenSteps
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
end OCaml.Vm.Boot.Startup
