import OCaml.Vm.Boot.Startup.LseekFileSteps
import OCaml.Vm.Boot.Startup.HtifReadEntryNormalized
import OCaml.Vm.Boot.Startup.HtifReadEntryImage
import OCaml.Vm.Boot.Startup.HtifReadCheckNormalized
import OCaml.Vm.Boot.Startup.HtifReadCheckImage
import OCaml.Vm.Boot.Startup.HtifReadClampNormalized
import OCaml.Vm.Boot.Startup.HtifReadClampImage
import OCaml.Vm.Boot.Startup.HtifReadCopyNormalized
import OCaml.Vm.Boot.Startup.HtifReadCopyImage
import OCaml.Vm.Boot.Startup.HtifReadCopyCallInterface
import OCaml.Vm.Boot.Startup.HtifReadAdvanceNormalized
import OCaml.Vm.Boot.Startup.HtifReadAdvanceImage
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! htif.c's `_read(3, buf, 16)` on "/prog" positioned 16 bytes before its
end: copy the trailer out of the embedded file and advance the position. -/

open Sail in
/-- `auipc a5; lw a5,-736(a5)` at 0x80000bf8: `fs_ready`. -/
theorem htif_read_ready_auipc : 2147486712#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 411543#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 3360#12 = BitVec.ofNat 64 Layout.sym_fs_ready := by decide

def htifReadLog (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 48 [(32, s0), (40, ra)]

theorem htifReadLog_inside {sp ra s0 : BitVec 64} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (htifReadLog sp ra s0) :=
  frame.word_log_inside fun off value member => by simp at member; omega

/-- `_read`: `fs_ready` is set; save `s0` and `ra`, keep `fd` in `s0`. -/
theorem htif_read_entry (c : Config) (sp ra s0 fd buf n : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, sp), (1, ra), (8, s0), (10, fd), (11, buf), (12, n)])
    (ready : read4 c.σ.mem Layout.sym_fs_ready = [1#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x80000bf8#64 (fun e => e = c) (WriteRegistersPost [15, 2, 8] (htifReadLog sp ra s0) c 0x80000c28#64 fd
      [(8, fd), (2, nativeStack sp 48), (15, 1#64), (1, ra), (10, fd), (11, buf), (12, n)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (htifReadLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput readX0bf8TSeg 0x80000bf8#64
        [(2, sp), (1, ra), (8, s0), (10, fd), (11, buf), (12, n)] [read4 c.σ.mem Layout.sym_fs_ready] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 10, 11, 12]; decide
      shape := by change ChainOK _ [2, 1, 8, 10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := htifReadEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code._read_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_fs_ready) 4 by constructor <;> decide).lw rfl
            (by simp only [htifreadentry_line_80000bf8, htifreadentry_line_80000bfc, eaddrM, srcVal, lookupG, runGM,
                  stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact htif_read_ready_auipc) (read4_pins _ _)
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_fs_ready)) 0#64 = true
          rw [ready]
          decide }))
  · simp only [readX0bf8TSeg, evalBlocks, evalBlock, SegEvalState.init, htifreadentry_line_80000bf8,
      htifreadentry_line_80000bfc, htifreadentry_line_80000c00, htifreadentry_line_80000c04,
      htifreadentry_line_80000c08, htifreadentry_line_80000c0c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, htifReadLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append]
    rw [show Functions.sign_extend (m := 64) 4048#12 = -BitVec.ofNat 64 48 by decide]
    rfl
  · rfl
  · simp only [readX0bf8TSeg, evalBlocks, evalBlock, SegEvalState.init, htifreadentry_line_80000bf8,
      htifreadentry_line_80000bfc, htifreadentry_line_80000c00, htifreadentry_line_80000c04,
      htifreadentry_line_80000c08, htifreadentry_line_80000c0c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of]
    rw [show Functions.sign_extend (m := 64) 4048#12 = -BitVec.ofNat 64 48 by decide, ready, open_se0,
      BitVec.add_zero]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨rfl, by decide⟩
  · rfl
  · decide

local macro "rsk" : tactic => `(tactic| simp only [htifreadcheck_line_80000c28, htifreadcheck_line_80000c30, htifreadcheck_line_80000c34, htifreadcheck_line_80000c38, htifreadcheck_line_80000c3c, htifreadcheck_line_80000c40, htifreadcheck_line_80000c44, htifreadcheck_line_80000c48, htifreadcheck_line_80000c50, htifreadcheck_line_80000c54, htifreadcheck_line_80000c5c, htifreadcheck_line_80000c64, htifreadcheck_line_80000c68, htifreadcheck_line_80000c70, htifreadcheck_line_80000c74, htifreadcheck_line_80000c78, htifreadcheck_line_80000c7c, htifreadcheck_line_80000c80, htifreadcheck_line_80000c84, htifreadcheck_line_80000c88, htifreadcheck_line_80000c8c, htifreadcheck_line_80000c94, htifreadcheck_line_80000c98, htifreadcheck_line_80000c9c, htifreadclamp_line_80000d10, htifreadclamp_line_80000d18, htifreadcopy_line_80000ca4, htifreadcopy_line_80000ca8, htifreadcopy_line_80000cac, htifreadcopy_line_80000cb0, htifreadcopy_line_80000cb4, htifreadcopy_line_80000cb8, htifreadcopy_line_80000cbc, htifreadcopy_line_80000cc0, htifreadcopy_line_80000cc4, htifreadcopy_line_80000cc8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

/-- The registers at `_read`'s copy: 16 bytes from position 0x249c of slot 1. -/
def htifReadChecked (sp buf : BitVec 64) : GRegs :=
  [(28, 16#64), (15, 16#64), (13, 0x24ac#64), (29, 0x249c#64), (16, 8#64), (10, BitVec.ofNat 64 Layout.sym_files),
    (6, 1#64), (17, BitVec.ofNat 64 Layout.sym_fds), (14, 6#64), (2, nativeStack sp 48), (8, 3#64), (11, buf),
    (12, 16#64)]

/-- `_read(3, buf, 16)` up to its `memcpy` call: descriptor 3 is "/prog"
positioned 16 bytes before its end. -/
theorem htif_read_check (c : Config) (sp ra buf : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(2, nativeStack sp 48), (8, 3#64), (10, 3#64), (11, buf), (12, 16#64)])
    (kind : read4 c.σ.mem (Layout.sym_fds + 72) = [4#8, 0#8, 0#8, 0#8])
    (flags : read4 c.σ.mem (Layout.sym_fds + 88) = [0#8, 0#8, 0#8, 0#8])
    (node : read4 c.σ.mem (Layout.sym_fds + 76) = [1#8, 0#8, 0#8, 0#8])
    (dir : (c.σ.mem[Layout.sym_files + 57]?).getD 0 = 0#8)
    (pos : bytesT c.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64)
    (size : bytesT c.σ.mem (Layout.sym_files + 88) 8 = 0x24ac#64)
 :
    FnSummary 0x80000c28#64 (fun e => e = c) (WriteRegistersPost [28, 15, 13, 29, 16, 10, 6, 17, 14] [] c 0x80000ca4#64
      (BitVec.ofNat 64 Layout.sym_files) (htifReadChecked sp buf)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (readX0c28FSeg ++ readX0c30FSeg ++ readX0c50FSeg ++ readX0c5cFSeg ++ readX0c64FSeg ++ readX0c70FSeg ++ readX0c94TSeg ++ readX0d10FSeg ++ readX0d18Seg) 0x80000c28#64
        [(2, nativeStack sp 48), (8, 3#64), (10, 3#64), (11, buf), (12, 16#64)]
        [[4#8, 0#8, 0#8, 0#8], [0#8, 0#8, 0#8, 0#8], [1#8, 0#8, 0#8, 0#8], [0#8],
          read8 c.σ.mem (Layout.sym_fds + 80), read8 c.σ.mem (Layout.sym_files + 88)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 10, 11, 12]; decide
      shape := by change ChainOK _ [2, 8, 10, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := htifReadCheck_code leaf.image
        chain_facts code with "Vsa.Sim.Code._read_at_"
        · rsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 72)) 4 by
              constructor <;> decide).lw rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 72)).toNat = Layout.sym_fds + 72 by decide]
            rw [← kind]; exact read4_pins _ _
          · rsk; simp only [wlogM]; trivial
        · rsk; decide
        · rsk; decide
        · rsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 88)) 4 by
              constructor <;> decide).lw rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 88)).toNat = Layout.sym_fds + 88 by decide]
            rw [← flags]; exact read4_pins _ _
          · rsk; simp only [wlogM]; trivial
        · rsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 76)) 4 by
              constructor <;> decide).lw rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 76)).toNat = Layout.sym_fds + 76 by decide]
            rw [← node]; exact read4_pins _ _
          · rsk; simp only [wlogM]; trivial
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 57)) 1 by
              constructor <;> decide).lbu rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_files + 57)).toNat = Layout.sym_files + 57 by decide]
            exact dir
          · rsk; simp only [wlogM]; trivial
        · rsk; decide
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 80)) 8 by
              constructor <;> decide).ld rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_fds + 80)).toNat = Layout.sym_fds + 80 by decide]
            exact read8_pins _ _
          · rsk; simp only [wlogM]; trivial
        · refine memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 88)) 8 by
              constructor <;> decide).ld rfl ?_ ?_) (fun _ => ?_)
          · rsk; decide
          · rw [show (BitVec.ofNat 64 (Layout.sym_files + 88)).toNat = Layout.sym_files + 88 by decide]
            exact read8_pins _ _
          · rsk; simp only [wlogM]; trivial
        · rsk; rw [read8_value, read8_value, pos, size]; decide
        · rsk; rw [read8_value, read8_value, pos, size]; decide }))
  · simp only [readX0c28FSeg, readX0c30FSeg, readX0c50FSeg, readX0c5cFSeg, readX0c64FSeg, readX0c70FSeg, readX0c94TSeg, readX0d10FSeg, readX0d18Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    rsk
    simp only [wlogM, List.nil_append]
  · rfl
  · simp only [readX0c28FSeg, readX0c30FSeg, readX0c50FSeg, readX0c5cFSeg, readX0c64FSeg, readX0c70FSeg, readX0c94TSeg, readX0d10FSeg, readX0d18Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    rsk
    simp only [read8_value, pos, size, htifReadChecked, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    repeat (first | exact And.intro (by decide) ?_ | decide)
  · rfl
  · decide

def htifReadSpillLog (sp : BitVec 64) : List WEntry := nativeWordLog sp 48 [(24, 6#64), (16, 16#64), (8, 16#64)]

theorem htifReadSpillLog_inside {sp : BitVec 64} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (htifReadSpillLog sp) :=
  frame.word_log_inside fun off value member => by simp at member; omega

/-- The registers at `_read`'s `memcpy(buf, data + 0x249c, 16)`. -/
def htifReadCopying (sp buf : BitVec 64) : GRegs :=
  [(11, 0x8680252c#64), (10, buf), (12, 16#64), (13, 0x86800090#64), (16, 56#64), (28, 16#64), (15, 16#64),
    (29, 0x249c#64), (6, 1#64), (17, BitVec.ofNat 64 Layout.sym_fds), (14, 6#64), (2, nativeStack sp 48), (8, 3#64)]

/-- `_read`'s copy: spill, then `memcpy(buf, data + 0x249c, 16)`. -/
theorem htif_read_copy_front (c : Config) (sp ra buf : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ (htifReadChecked sp buf))
    (data : bytesT c.σ.mem (Layout.sym_files + 80) 8 = 0x86800090#64) :
    FnSummary 0x80000ca4#64 (fun e => e = c) (WriteRegistersPost [11, 10, 12, 13, 16] (htifReadSpillLog sp) c
      jal_80000ccc_call.pc buf (htifReadCopying sp buf)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (htifReadSpillLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput readX0ca4Seg 0x80000ca4#64 (htifReadChecked sp buf)
        [read8 c.σ.mem (Layout.sym_files + 80)] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [28, 15, 13, 29, 16, 10, 6, 17, 14, 2, 8, 11, 12]; decide
      shape := by change ChainOK _ [28, 15, 13, 29, 16, 10, 6, 17, 14, 2, 8, 11, 12] _; decide
      tick := leaf.tick
      facts := by
        have code := htifReadCopy_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 48) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 48 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code._read_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 (Layout.sym_files + 80)) 8 by constructor <;> decide).ld rfl
            (by simp only [htifreadcopy_line_80000ca4, htifreadcopy_line_80000ca8, htifreadcopy_line_80000cac, htifreadcopy_line_80000cb0, htifreadcopy_line_80000cb4, htifreadcopy_line_80000cb8, htifreadcopy_line_80000cbc, htifreadcopy_line_80000cc0, htifreadcopy_line_80000cc4, htifreadcopy_line_80000cc8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff, htifReadChecked]; decide)
            (by rw [show (BitVec.ofNat 64 (Layout.sym_files + 80)).toNat = Layout.sym_files + 80 by decide]
                exact read8_pins _ _)
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · simp only [readX0ca4Seg, evalBlocks, evalBlock, SegEvalState.init, htifreadcopy_line_80000ca4, htifreadcopy_line_80000ca8, htifreadcopy_line_80000cac, htifreadcopy_line_80000cb0, htifreadcopy_line_80000cb4, htifreadcopy_line_80000cb8, htifreadcopy_line_80000cbc, htifreadcopy_line_80000cc0, htifreadcopy_line_80000cc4, htifreadcopy_line_80000cc8, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, htifReadChecked, htifReadSpillLog, nativeWordLog, List.map, List.nil_append, List.cons_append, read8_value, data]
    rw [show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide,
      show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide,
      show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
  · rfl
  · simp only [readX0ca4Seg, evalBlocks, evalBlock, SegEvalState.init, htifreadcopy_line_80000ca4, htifreadcopy_line_80000ca8, htifreadcopy_line_80000cac, htifreadcopy_line_80000cb0, htifreadcopy_line_80000cb4, htifreadcopy_line_80000cb8, htifreadcopy_line_80000cbc, htifreadcopy_line_80000cc0, htifreadcopy_line_80000cc4, htifreadcopy_line_80000cc8, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, htifReadChecked, htifReadSpillLog, nativeWordLog, List.map, List.nil_append, List.cons_append, read8_value, data]
    simp only [htifReadCopying, open_se0, BitVec.add_zero, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    repeat (first | exact And.intro (by decide) ?_ | decide)
  · rfl
  · decide

theorem htif_read_copy_call (c : Config) (sp ra buf : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ (htifReadChecked sp buf))
    (data : bytesT c.σ.mem (Layout.sym_files + 80) 8 = 0x86800090#64) :
    FnSummary 0x80000ca4#64 (fun e => e = c)
      (WriteRegistersPost ([11, 10, 12, 13, 16] ++ [1]) (htifReadSpillLog sp) c jal_80000ccc_call.target buf
        ((1, jal_80000ccc_call.link) :: htifReadCopying sp buf)) :=
  block_then_call c jal_80000ccc_call_shape jal_80000ccc_call_decode (fun _ h => jal_80000ccc_call_pins h)
    (htif_read_copy_front c sp ra buf leaf frame regs data) (by simp only [htifReadCopying, keysG]; decide)
    (by simp only [htifReadCopying, KeysAvoidRa, keysG]; decide) rfl

local macro "ask" : tactic => `(tactic| simp only [htifreadadvance_line_80000cd0, htifreadadvance_line_80000cd4, htifreadadvance_line_80000cd8, htifreadadvance_line_80000cdc, htifreadadvance_line_80000ce0, htifreadadvance_line_80000ce4, htifreadadvance_line_80000ce8, htifreadadvance_line_80000cec, htifreadadvance_line_80000cf0, htifreadadvance_line_80000cf4, htifreadadvance_line_80000cf8, htifreadadvance_line_80000cfc, htifreadadvance_line_80000d00, htifreadadvance_line_80000d04, htifreadadvance_line_80000d08, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, imm20Of, ldsRunM, stepLdsM, List.headD_cons, List.tail_cons])

def htifReadAdvanceLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [read8 m (nativeFrameBase sp 48 + 24), read8 m (nativeFrameBase sp 48 + 8), read8 m (Layout.sym_fds + 80),
    read8 m (nativeFrameBase sp 48 + 16), read8 m (nativeFrameBase sp 48 + 40), read8 m (nativeFrameBase sp 48 + 32)]

/-- `_read` after `memcpy`: advance fds[3]'s position by 16; restore and return 16. -/
theorem htif_read_advance (c : Config) (sp ra s0 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, nativeStack sp 48), (8, 3#64)])
    (spill : ∀ off value, (off, value) ∈ [(24, 6#64), (16, 16#64), (8, 16#64), (40, ra), (32, s0)] →
      bytesT c.σ.mem (nativeFrameBase sp 48 + off) 8 = value)
    (pos : bytesT c.σ.mem (Layout.sym_fds + 80) 8 = 0x249c#64) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80000cd0#64 (fun e => e = c)
      (WriteRegistersPost [2, 10, 8, 1, 14, 28, 17, 15] [(Layout.sym_fds + 80, 8, 0x24ac#64)] c ra 16#64
        [(2, sp), (10, 16#64), (8, s0), (1, ra), (14, 0x24ac#64), (28, 16#64),
          (17, BitVec.ofNat 64 (Layout.sym_fds + 72)), (15, 16#64)]) := by
  have savedRa := spill 40 ra (by simp)
  have s24 := spill 24 6#64 (by simp)
  have s8 := spill 8 16#64 (by simp)
  have s16 := spill 16 16#64 (by simp)
  have s32 := spill 32 s0 (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput readX0cd0Seg 0x80000cd0#64 [(2, nativeStack sp 48), (8, 3#64)]
        (htifReadAdvanceLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8]; decide
      shape := by change ChainOK _ [2, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := htifReadAdvance_code leaf.image
        chain_facts code with "Vsa.Sim.Code._read_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl (by ask; rfl) (frame.pins_slot c (by decide))
        · iterate 3 refine memFacts_stepMem_skip rfl ?_
          exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl (by ask; rfl) (frame.pins_slot c (by decide))
        · iterate 7 refine memFacts_stepMem_skip rfl ?_
          exact (show ReadWindow (BitVec.ofNat 64 (Layout.sym_fds + 80)) 8 by constructor <;> decide).ld rfl
            (by ask; simp only [htifReadAdvanceLoads, List.headD_cons, read8_value, s24]; decide)
            (by rw [show (BitVec.ofNat 64 (Layout.sym_fds + 80)).toNat = Layout.sym_fds + 80 by decide]
                exact read8_pins _ _)
        · iterate 8 refine memFacts_stepMem_skip rfl ?_
          exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl (by ask; rfl) (frame.pins_slot c (by decide))
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 80)) 8 by constructor <;> decide).sd rfl
            (by ask; simp only [htifReadAdvanceLoads, List.headD_cons, read8_value, s24]; decide)
        · refine memFacts_stepMem_store rfl ?_ (fun _ => by
              ask
              simp only [wentryM, widthOfM, OutLRange, and_true]
              ask
              simp only [htifReadAdvanceLoads, List.headD_cons, read8_value, s24]
              refine Or.inr (Nat.le_trans (m := heapEnd) (by decide) ?_)
              rw [show Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 by decide, nativeStack,
                frame.address 40 (by decide), frame.slot_nat (by decide)]
              have := frame.lower
              unfold nativeFrameBase
              omega)
          iterate 10 refine memFacts_stepMem_skip rfl ?_
          exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl (by ask; rfl) (frame.pins_slot c (by decide))
        · refine memFacts_stepMem_skip rfl (memFacts_stepMem_store rfl ?_ (fun _ => by
              ask
              simp only [wentryM, widthOfM, OutLRange, and_true]
              ask
              simp only [htifReadAdvanceLoads, List.headD_cons, read8_value, s24]
              refine Or.inr (Nat.le_trans (m := heapEnd) (by decide) ?_)
              rw [show Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 by decide, nativeStack,
                frame.address 32 (by decide), frame.slot_nat (by decide)]
              have := frame.lower
              unfold nativeFrameBase
              omega))
          iterate 10 refine memFacts_stepMem_skip rfl ?_
          exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl (by ask; rfl) (frame.pins_slot c (by decide))
        · ask
          simp only [htifReadAdvanceLoads, List.tail_cons, List.headD_cons]
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · simp only [readX0cd0Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    ask
    simp only [wlogM, wentryM, widthOfM]
    ask
    simp only [htifReadAdvanceLoads, List.headD_cons, List.tail_cons, read8_value, s24, s8, s16, s32, savedRa, pos]
    simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq, and_true]
    exact ⟨by decide, by decide⟩
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [readX0cd0Seg, evalBlocks, evalBlock, SegEvalState.init, List.cons_append, List.nil_append]
    ask
    simp only [htifReadAdvanceLoads, List.headD_cons, List.tail_cons, read8_value, s24, s8, s16, s32, savedRa, pos]
    rw [show Functions.sign_extend (m := 64) 48#12 = BitVec.ofNat 64 48 by decide, nativeStack_restore]
    simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    repeat (first | exact And.intro (by decide) ?_ | decide)
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
