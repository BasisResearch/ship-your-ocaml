import OCaml.Vm.Boot.Startup.OpenSteps
import OCaml.Vm.Boot.Startup.OpenProgSteps
import OCaml.Vm.Boot.Startup.ReentWrappers
import OCaml.Vm.Boot.Startup.HtifLseekEntryNormalized
import OCaml.Vm.Boot.Startup.HtifLseekEntryImage
import OCaml.Vm.Boot.Startup.HtifLseekCheckNormalized
import OCaml.Vm.Boot.Startup.HtifLseekCheckImage
import OCaml.Vm.Boot.Startup.HtifLseekEndNormalized
import OCaml.Vm.Boot.Startup.HtifLseekEndImage
import OCaml.Vm.Boot.Startup.HtifLseekSignNormalized
import OCaml.Vm.Boot.Startup.HtifLseekSignImage
import OCaml.Vm.Boot.Startup.HtifLseekStoreNormalized
import OCaml.Vm.Boot.Startup.HtifLseekStoreImage
import OCaml.Vm.Boot.Startup.HtifLseekNegNormalized
import OCaml.Vm.Boot.Startup.HtifLseekNegImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `lseek(fd, off, SEEK_END)` on a file descriptor: newlib's `lseek` →
`_lseek_r` → htif.c's `_lseek`, which sets the position to the file's size
plus `off`. -/

open Sail in
/-- `auipc a5; lw a5,-1920(a5)` at 0x80001098: `fs_ready`. -/
theorem htif_lseek_ready_auipc : 2147487896#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 411543#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2176#12 = BitVec.ofNat 64 Layout.sym_fs_ready := by decide

def htifLseekLog (sp ra : BitVec 64) : List WEntry := nativeWordLog sp 48 [(40, ra)]

theorem htifLseekLog_inside {sp ra : BitVec 64} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (htifLseekLog sp ra) :=
  frame.word_log_inside fun off value member => by simp at member; omega

/-- `_lseek`: `fs_ready` is set; save `ra`. -/
theorem htif_lseek_entry (c : Config) (sp ra fd off whence : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, sp), (1, ra), (10, fd), (11, off), (12, whence)])
    (ready : read4 c.σ.mem Layout.sym_fs_ready = [1#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x80001098#64 (fun e => e = c) (WriteRegistersPost [15, 2] (htifLseekLog sp ra) c 0x800010c8#64 fd
      [(2, nativeStack sp 48), (15, 1#64), (1, ra), (10, fd), (11, off), (12, whence)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (htifLseekLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput lseekX1098TSeg 0x80001098#64 [(2, sp), (1, ra), (10, fd), (11, off), (12, whence)]
        [read4 c.σ.mem Layout.sym_fs_ready] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 10, 11, 12]; decide
      shape := by change ChainOK _ [2, 1, 10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := htifLseekEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code._lseek_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_fs_ready) 4 by constructor <;> decide).lw rfl
            (by simp only [htiflseekentry_line_80001098, htiflseekentry_line_8000109c, htiflseekentry_line_800010a0, htiflseekentry_line_800010a4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact htif_lseek_ready_auipc) (read4_pins _ _)
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_fs_ready)) 0#64 = true
          rw [ready]
          decide }))
  · simp only [lseekX1098TSeg, evalBlocks, evalBlock, SegEvalState.init, htiflseekentry_line_80001098, htiflseekentry_line_8000109c, htiflseekentry_line_800010a0, htiflseekentry_line_800010a4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, htifLseekLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append]
    rw [show Functions.sign_extend (m := 64) 4048#12 = -BitVec.ofNat 64 48 by decide]
    rfl
  · rfl
  · simp only [lseekX1098TSeg, evalBlocks, evalBlock, SegEvalState.init, htiflseekentry_line_80001098, htiflseekentry_line_8000109c, htiflseekentry_line_800010a0, htiflseekentry_line_800010a4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of]
    rw [show Functions.sign_extend (m := 64) 4048#12 = -BitVec.ofNat 64 48 by decide, ready]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨rfl, by decide⟩
  · rfl
  · decide

/-- A store step: a later access sees the store's write log. -/
theorem memFacts_stepMem_store {m : Std.ExtHashMap Nat (BitVec 8)} {a b : MInstr} {L L' : GRegs}
    {bs : List (BitVec 8)} (kind : IsStore a.kind = true) (h : MemFacts m L' bs b)
    (miss : IsLoad b.kind = true → OutLRange [wentryM a L] (eaddrM b L').toNat (widthOfM b.kind)) :
    MemFacts (stepMemM m a L) L' bs b := by
  rw [stepMemM_store kind]; exact memFacts_writeLog h miss

local macro "lsk" : tactic => `(tactic| simp only [htiflseekcheck_line_800010c8, htiflseekcheck_line_800010d0, htiflseekcheck_line_800010d4, htiflseekcheck_line_800010d8, htiflseekcheck_line_800010dc, htiflseekcheck_line_800010e0, htiflseekcheck_line_800010e4, htiflseekcheck_line_800010e8, htiflseekcheck_line_800010f0, htiflseekcheck_line_800010f8, htiflseekend_line_8000114c, htiflseekend_line_80001150, htiflseekend_line_80001154, htiflseekend_line_80001158, htiflseekend_line_8000115c, htiflseekend_line_80001160, htiflseekend_line_80001164, htiflseekend_line_80001168, htiflseekend_line_80001170, htiflseekneg_line_80001130, htiflseekstore_line_80001110, htiflseekstore_line_80001114, htiflseekstore_line_80001118, htiflseekstore_line_8000111c, htiflseekstore_line_80001120, htiflseekstore_line_80001124, htiflseekstore_line_80001128, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- `_lseek(3, -16, SEEK_END)` on the file in slot 1: position = size - 16. -/
theorem htif_lseek_end (c : Config) (sp ra off : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (1, ra), (10, 3#64), (11, off), (12, 2#64)])
    (kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8])
    (node : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8])
    (dir : (c.σ.mem[Layout.sym_files + 57]?).getD 0 = 0#8)
    (size : bytesT c.σ.mem (Layout.sym_files + 88) 8 = 0x24ac#64)
    (saved : bytesT c.σ.mem (nativeFrameBase sp 48 + 40) 8 = ra)
    (neg : guardB bop.BLT off 0#64 = true) (fits : guardB bop.BGE 0x24ac#64 (0#64 - off) = true) :
    FnSummary 0x800010c8#64 (fun e => e = c) (WriteRegistersPost [15, 13, 16, 17, 14, 6, 12, 10, 2, 1] [(Layout.sym_fds + 80, 8, 0x24ac#64 + off)] c ra (0x24ac#64 + off)
        [(2, sp), (1, ra), (10, 0x24ac#64 + off), (16, BitVec.ofNat 64 (Layout.sym_fds + 72)), (15, 72#64), (13, 0#64 - off),
          (14, 0x24ac#64), (12, 1#64), (6, 4#64), (17, 4#64), (11, off)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (lseekX10c8FSeg ++ lseekX10d0FSeg ++ lseekX10f0FSeg ++ lseekX10f8FSeg ++ lseekX1100TSeg ++ lseekX114cFSeg ++ lseekX1170Seg ++ lseekX110cTSeg ++ lseekX1130TSeg ++ lseekX1110Seg) 0x800010c8#64
        [(2, nativeStack sp 48), (1, ra), (10, 3#64), (11, off), (12, 2#64)]
        [[4#8, 0#8, 0#8, 0#8], [1#8, 0#8, 0#8, 0#8], [0#8], read8 c.σ.mem (Layout.sym_files + 88),
          read8 c.σ.mem (nativeFrameBase sp 48 + 40)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 10, 11, 12]; decide
      shape := by change ChainOK _ [2, 1, 10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := htifLseekCheck_code leaf.image
        chain_facts code with "Vsa.Sim.Code._lseek_at_"
        · lsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 72)) 4 by
              constructor <;> decide).lw rfl ?_ ?_) (fun _ => ?_)
          · lsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 72)).toNat = Layout.sym_fds + 72 by decide, ← kind]
            exact read4_pins _ _
          · lsk; simp only [wlogM]; trivial
        · lsk; decide
        · lsk; decide
        · lsk; decide
        · lsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 76)) 4 by
              constructor <;> decide).lw rfl ?_ ?_) (fun _ => ?_)
          · lsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 76)).toNat = Layout.sym_fds + 76 by decide, ← node]
            exact read4_pins _ _
          · lsk; simp only [wlogM]; trivial
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 57)) 1 by
              constructor <;> decide).lbu rfl ?_ ?_) (fun _ => ?_)
          · lsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_files + 57)).toNat = Layout.sym_files + 57 by decide]
            exact dir
          · lsk; simp only [wlogM]; trivial
        · lsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 88)) 8 by
              constructor <;> decide).ld rfl ?_ ?_) (fun _ => ?_)
          · lsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_files + 88)).toNat = Layout.sym_files + 88 by decide]
            exact read8_pins _ _
          · lsk; simp only [wlogM]; trivial
        · lsk; exact neg
        · lsk; rw [read8_value, size]; exact fits
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 80)) 8 by constructor <;> decide).sd rfl
            (by lsk; decide)
        · refine memFacts_stepMem_store rfl (memFacts_stepMem_skip rfl (memFacts_stepMem_skip rfl
            (memFacts_stepMem_skip rfl (memFacts_stepMem_skip rfl (memFacts_writeLog
              ((frame.read_slot (off := 40) (by decide) (by decide)).ld rfl (by lsk; rfl)
                (frame.pins_slot c (by decide))) (fun _ => by lsk; simp only [wlogM]; trivial)))))) (fun _ => ?_)
          lsk
          simp only [wentryM, widthOfM, OutLRange, and_true]
          lsk
          refine Or.inr (Nat.le_trans (m := heapEnd) (by decide) ?_)
          rw [show Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 by decide, nativeStack,
            frame.address 40 (by decide), frame.slot_nat (by decide)]
          have := frame.lower
          unfold nativeFrameBase
          omega
        · lsk
          rw [read8_value, saved, ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · simp only [lseekX10c8FSeg, lseekX10d0FSeg, lseekX10f0FSeg, lseekX10f8FSeg, lseekX1100TSeg, lseekX114cFSeg, lseekX1170Seg, lseekX110cTSeg, lseekX1130TSeg, lseekX1110Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    lsk
    simp only [wlogM, wentryM, widthOfM]
    lsk
    simp only [read8_value, size, List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true]
    repeat (first | exact And.intro (by decide) ?_ | decide | rfl)
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, saved, ret_tgt ra leaf.aligned]
  · simp only [lseekX10c8FSeg, lseekX10d0FSeg, lseekX10f0FSeg, lseekX10f8FSeg, lseekX1100TSeg, lseekX114cFSeg, lseekX1170Seg, lseekX110cTSeg, lseekX1130TSeg, lseekX1110Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    lsk
    simp only [read8_value, size, saved, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    rw [show Functions.sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 by decide, nativeStack_restore]
    repeat' constructor
    all_goals decide
  · rfl
  · decide

end OCaml.Vm.Boot.Startup
