import OCaml.Vm.Boot.Startup.ResolveRun
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

/-! htif.c's `resolve(path, r)` once the file system is up, for "/prog":
the leading '/' is an empty component, and "prog" is slot 1 (`R_FILE`). -/

def resolveEnteredReady (sp ra s4 path r : BitVec 64) : GRegs :=
  [(19, r), (25, path), (2, nativeStack sp 96), (15, 1#64), (1, ra), (20, s4), (10, path), (11, r)]

/-- A later `resolve`: `fs_ready` is set, so `fs_init` is skipped. -/
theorem resolve_entry_ready (c : Config) (sp ra s3 s4 s9 path r : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (resolveInput sp ra s3 s4 s9 path r))
    (ready : read4 c.σ.mem Layout.sym_fs_ready = [1#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x8000056c#64 (fun e => e = c)
      (WriteRegistersPost [19, 25, 2, 15] (resolveLog sp ra s3 s4 s9) c 0x80000598#64 path
        (resolveEnteredReady sp ra s4 path r)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (resolveLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput resolveX056cTSeg 0x8000056c#64 (resolveInput sp ra s3 s4 s9 path r)
        [read4 c.σ.mem Layout.sym_fs_ready] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 19, 25, 1, 20, 10, 11]; decide
      shape := by change ChainOK _ [2, 19, 25, 1, 20, 10, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 96) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 96 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_fs_ready) 4 by constructor <;> decide).lw rfl
            (by simp only [resolveentry_line_8000056c, resolveentry_line_80000570, resolveentry_line_80000574, resolveentry_line_80000578, resolveentry_line_8000057c, resolveentry_line_80000580, resolveentry_line_80000584, resolveentry_line_80000588, resolveentry_line_8000058c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact resolve_ready_auipc) (read4_pins _ _)
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (slot 88 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_fs_ready)) 0#64 = true
          rw [ready]
          decide }))
  · simp only [resolveX056cTSeg, evalBlocks, evalBlock, SegEvalState.init, resolveentry_line_8000056c, resolveentry_line_80000570, resolveentry_line_80000574, resolveentry_line_80000578, resolveentry_line_8000057c, resolveentry_line_80000580, resolveentry_line_80000584, resolveentry_line_80000588, resolveentry_line_8000058c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveInput, imm20Of, resolveLog,
      resolveSlots, nativeWordLog, List.map, List.nil_append, List.cons_append]
    rw [show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide]
    rfl
  · rfl
  · simp only [resolveX056cTSeg, evalBlocks, evalBlock, SegEvalState.init, resolveentry_line_8000056c, resolveentry_line_80000570, resolveentry_line_80000574, resolveentry_line_80000578, resolveentry_line_8000057c, resolveentry_line_80000580, resolveentry_line_80000584, resolveentry_line_80000588, resolveentry_line_8000058c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveInput, imm20Of]
    rw [show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero, ready]
    simp only [resolveEnteredReady, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨rfl, by decide⟩
  · rfl
  · decide

/-- The last component starts after the path's first byte, a '/' (`b = 1`):
clear `r->last_dotdot`, start at the root. -/
theorem resolve_back_rooted (c : Config) (spo path len ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame spo 80)
    (regs : GHolds c.σ [(14, 1#64), (11, 47#64), (15, len), (10, len), (25, path), (19, nativeStack spo 80)])
    (window : ReadWindow path 1) (slash : (c.σ.mem[path.toNat]?).getD 0 = 47#8)
    (nonzero : len ≠ 0#64) (notTwo : len - 1#64 ≠ 1#64) (notThree : len - 1#64 ≠ 2#64) :
    FnSummary 0x800007d0#64 (fun e => e = c) (WriteRegistersPost [20, 15, 13, 12] [(resAt spo 44, 4, 0#64)] c
      0x8000062c#64 len [(20, 0#64), (15, 0#64), (13, 2#64), (12, nameByteWord 47#8), (14, 1#64), (11, 47#64), (10, len),
        (25, path), (19, nativeStack spo 80)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (by
      have lower := frame.lower
      simp only [LogInW, InsideW, resAt_nat frame (by decide : 44 ≤ 80), or_false, and_true]
      unfold nativeFrameBase at *; omega))
    (block_summary _ _ _ _ _ (show BlockInput (resolveX07d0FSeg ++ resolveX07dcFSeg ++ resolveX07e4TSeg ++
        resolveX0604TSeg ++ resolveX061cFSeg) 0x800007d0#64
        [(14, 1#64), (11, 47#64), (15, len), (10, len), (25, path), (19, nativeStack spo 80)] [[47#8]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 11, 15, 10, 25, 19]; decide
      shape := by change ChainOK _ [14, 11, 15, 10, 25, 19] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveBackTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · change guardB bop.BEQ 1#64 0#64 = false
          decide
        · exact window.lbu rfl (by
            simp only [resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
              ite_false, Nat.reduceEqDiff]
            rw [show (1#64 : BitVec 64) + Functions.sign_extend (m := 64) 4095#12 = 0#64 by decide,
              BitVec.add_zero, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) slash
        · change guardB bop.BNE (bytesVal .lbu [47#8]) 47#64 = false
          decide
        · change guardB bop.BNE (len - 1#64) (0#64 + Functions.sign_extend (m := 64) 1#12) = true
          rw [show 0#64 + Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]
          exact bne_iff_ne.mpr notTwo
        · change guardB bop.BNE (len - 1#64) (0#64 + Functions.sign_extend (m := 64) 2#12) = true
          rw [show 0#64 + Functions.sign_extend (m := 64) 2#12 = 2#64 by decide]
          exact bne_iff_ne.mpr notThree
        · exact (show WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 44) 4 by
            rw [nativeStack, frame.address 44 (by decide)]; exact frame.word32 (by decide) (by decide)).sw rfl (by
            simp only [resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
              ite_false, Nat.reduceEqDiff]
            rw [show Functions.sign_extend (m := 64) 44#12 = 44#64 by decide])
        · change guardB bop.BEQ len 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · simp only [resolveX07d0FSeg, resolveX07dcFSeg, resolveX07e4TSeg, resolveX0604TSeg, resolveX061cFSeg, evalBlocks,
      evalBlock, SegEvalState.init, resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      imm20Of, List.cons_append, List.nil_append, resAt, show Functions.sign_extend (m := 64) 44#12 = 44#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.zero_add]
  · rfl
  · simp only [resolveX07d0FSeg, resolveX07dcFSeg, resolveX07e4TSeg, resolveX0604TSeg, resolveX061cFSeg, evalBlocks,
      evalBlock, SegEvalState.init, resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      imm20Of, List.cons_append, List.nil_append, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide,
      show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide, BitVec.zero_add]
    rw [name_lbu_value]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
