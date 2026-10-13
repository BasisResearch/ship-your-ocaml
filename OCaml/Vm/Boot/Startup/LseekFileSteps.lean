import OCaml.Vm.Boot.Startup.OpenSteps
import OCaml.Vm.Boot.Startup.OpenProgSteps
import OCaml.Vm.Boot.Startup.LibLseekNormalized
import OCaml.Vm.Boot.Startup.LibLseekImage
import OCaml.Vm.Boot.Startup.LseekREntryNormalized
import OCaml.Vm.Boot.Startup.LseekREntryImage
import OCaml.Vm.Boot.Startup.LseekRReturnNormalized
import OCaml.Vm.Boot.Startup.LseekRReturnImage
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
/-- `auipc a0; ld a0,896(a0)` at 0x80042578: `_impure_ptr`. -/
theorem lseek_impure_auipc : 2147755384#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 140567#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 896#12 = BitVec.ofNat 64 allocatorImpureAddr := by decide

/-- `lseek`: move the arguments up one and load `_impure_ptr`. -/
theorem lib_lseek (c : Config) (fd off whence ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, fd), (11, off), (12, whence)]) :
    FnSummary 0x80042574#64 (fun e => e = c)
      (WriteRegistersPost [14, 10, 13, 12, 11] [] c 0x80042328#64 (getenvReent c)
        [(11, fd), (12, off), (13, whence), (10, getenvReent c), (14, fd)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput lseekX2574Seg 0x80042574#64 [(10, fd), (11, off), (12, whence)]
        [read8 c.σ.mem allocatorImpureAddr] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 11, 12]; decide
      shape := by change ChainOK _ [10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := libLseek_code leaf.image
        chain_facts code with "Vsa.Sim.Code.lseek_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 by constructor <;> decide).ld rfl
            (by simp only [liblseek_line_80042574, liblseek_line_80042578, liblseek_line_8004257c, liblseek_line_80042580, liblseek_line_80042584, liblseek_line_80042588, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, imm20Of, Nat.reduceEqDiff]
                exact lseek_impure_auipc) (read8_pins _ _) }))
  · rfl
  · rfl
  · simp only [lseekX2574Seg, evalBlocks, evalBlock, SegEvalState.init, liblseek_line_80042574, liblseek_line_80042578, liblseek_line_8004257c, liblseek_line_80042580, liblseek_line_80042584, liblseek_line_80042588, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, getenvReent, read8_value, open_se0, BitVec.add_zero]
  · rfl
  · decide

open Sail in
/-- `auipc a5; sw zero,-1536(a5)` at 0x80042348: the global `errno`. -/
theorem lseek_r_errno_auipc : 2147754824#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 145303#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2560#12 = BitVec.ofNat 64 0x80064d48 := by decide

open Sail in
theorem lseek_r_a5_auipc : 2147754824#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 145303#32 +++ 0#12) =
    0x80065348#64 := by decide

/-- `_lseek_r`: save, clear the global `errno`, call `_lseek(fd, off, whence)`. -/
theorem lseek_r_entry (c : Config) (sp ra s0 reent fd off whence : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ (openRInput sp ra s0 reent fd off whence)) :
    FnSummary 0x80042328#64 (fun e => e = c) (WriteRegistersPost [15, 10, 12, 8, 11, 2] (openRLog sp ra s0) c 0x80042350#64 fd
      [(15, 0x80065348#64), (10, fd), (12, whence), (8, reent), (11, off), (2, nativeStack sp 16), (1, ra),
        (13, whence)]) := by
  apply registers_of_blocks leaf.image (imageOutside_append (frame.image_outside (frame.word_log_inside
      fun off value member => by simp at member; omega)) (by constructor <;> simp only [OutLRange] <;> decide))
    (block_summary _ _ _ _ _ (show BlockInput lseek_rX2328Seg 0x80042328#64 (openRInput sp ra s0 reent fd off whence)
        [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 10, 11, 12, 13]; decide
      shape := by change ChainOK _ [2, 1, 8, 10, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := lseekREntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 16) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 16 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code._lseek_r_at_"
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064d48) 4 by constructor <;> decide).sw rfl
            (by simp only [lseekrentry_line_80042328, lseekrentry_line_8004232c, lseekrentry_line_80042330, lseekrentry_line_80042334, lseekrentry_line_80042338, lseekrentry_line_8004233c, lseekrentry_line_80042340, lseekrentry_line_80042344, lseekrentry_line_80042348, lseekrentry_line_8004234c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact lseek_r_errno_auipc) }))
  · simp only [lseek_rX2328Seg, evalBlocks, evalBlock, SegEvalState.init, lseekrentry_line_80042328, lseekrentry_line_8004232c, lseekrentry_line_80042330, lseekrentry_line_80042334, lseekrentry_line_80042338, lseekrentry_line_8004233c, lseekrentry_line_80042340, lseekrentry_line_80042344, lseekrentry_line_80042348, lseekrentry_line_8004234c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of, openRLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append, lseek_r_errno_auipc,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
    rfl
  · rfl
  · simp only [lseek_rX2328Seg, evalBlocks, evalBlock, SegEvalState.init, lseekrentry_line_80042328, lseekrentry_line_8004232c, lseekrentry_line_80042330, lseekrentry_line_80042334, lseekrentry_line_80042338, lseekrentry_line_8004233c, lseekrentry_line_80042340, lseekrentry_line_80042344, lseekrentry_line_80042348, lseekrentry_line_8004234c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, lseek_r_a5_auipc]
    rfl
  · rfl
  · decide

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
theorem htif_lseek_end (c : Config) (sp ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (1, ra), (10, 3#64), (11, -16#64), (12, 2#64)])
    (kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8])
    (node : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8])
    (dir : (c.σ.mem[Layout.sym_files + 57]?).getD 0 = 0#8)
    (size : bytesT c.σ.mem (Layout.sym_files + 88) 8 = 0x24ac#64)
    (saved : bytesT c.σ.mem (nativeFrameBase sp 48 + 40) 8 = ra) :
    FnSummary 0x800010c8#64 (fun e => e = c) (WriteRegistersPost [15, 13, 16, 17, 14, 6, 12, 10, 2, 1] [(Layout.sym_fds + 80, 8, 0x249c#64)] c ra 0x249c#64
        [(2, sp), (1, ra), (10, 0x249c#64), (16, BitVec.ofNat 64 (Layout.sym_fds + 72)), (15, 72#64), (13, 16#64),
          (14, 0x24ac#64), (12, 1#64), (6, 4#64), (17, 4#64), (11, -16#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (lseekX10c8FSeg ++ lseekX10d0FSeg ++ lseekX10f0FSeg ++ lseekX10f8FSeg ++ lseekX1100TSeg ++ lseekX114cFSeg ++ lseekX1170Seg ++ lseekX110cTSeg ++ lseekX1130TSeg ++ lseekX1110Seg) 0x800010c8#64
        [(2, nativeStack sp 48), (1, ra), (10, 3#64), (11, -16#64), (12, 2#64)]
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
        · lsk; decide
        · lsk; rw [read8_value, size]; decide
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
    exact ⟨by decide, by decide⟩
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

/-- `_lseek` succeeded: restore and return its result. -/
theorem lseek_r_succeed (c : Config) (sp ra s0 v oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ [(10, v), (2, nativeStack sp 16)]) (ok : v ≠ -1#64)
    (saved : ∀ off value, (off, value) ∈ [(8, ra), (0, s0)] →
      bytesT c.σ.mem (nativeFrameBase sp 16 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80042354#64 (fun e => e = c)
      (WriteRegistersPost [2, 8, 1, 15] [] c ra v [(2, sp), (8, s0), (1, ra), (15, -1#64), (10, v)]) := by
  have savedRa := saved 8 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (lseek_rX2354FSeg ++ lseek_rX235cSeg) 0x80042354#64
        [(10, v), (2, nativeStack sp 16)]
        [read8 c.σ.mem (nativeFrameBase sp 16 + 8), read8 c.σ.mem (nativeFrameBase sp 16 + 0)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := lseekRReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code._lseek_r_at_"
        · change guardB bop.BEQ v (0#64 + Functions.sign_extend (m := 64) 4095#12) = false
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
  · simp only [lseek_rX2354FSeg, lseek_rX235cSeg, evalBlocks, evalBlock, SegEvalState.init, lseekrreturn_line_80042354, lseekrreturn_line_8004235c, lseekrreturn_line_80042360, lseekrreturn_line_80042364, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, read8_value,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, nativeStack_restore, savedRa,
      saved 0 s0 (by simp), show 0#64 + Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
