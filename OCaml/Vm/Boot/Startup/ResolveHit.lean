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
end OCaml.Vm.Boot.Startup
