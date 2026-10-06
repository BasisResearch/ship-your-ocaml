import OCaml.Vm.Boot.Startup.ResolveEntryNormalized
import OCaml.Vm.Boot.Startup.ResolveEntryImage
import OCaml.Vm.Boot.Startup.ResolveEntryCallInterface
import OCaml.Vm.Boot.Startup.ResolveClearNormalized
import OCaml.Vm.Boot.Startup.ResolveClearImage
import OCaml.Vm.Boot.Startup.ResolveClearCallInterface
import OCaml.Vm.Boot.Startup.ResolveSlashNormalized
import OCaml.Vm.Boot.Startup.ResolveSlashImage
import OCaml.Vm.Boot.Startup.ResolveLastNormalized
import OCaml.Vm.Boot.Startup.ResolveLastImage
import OCaml.Vm.Boot.Startup.ResolveEndNormalized
import OCaml.Vm.Boot.Startup.ResolveEndImage
import OCaml.Vm.Boot.Startup.ResolveBackNormalized
import OCaml.Vm.Boot.Startup.ResolveBackImage
import OCaml.Vm.Boot.Startup.ResolveBackTestNormalized
import OCaml.Vm.Boot.Startup.ResolveBackTestImage
import OCaml.Vm.Boot.Startup.ResolveBackByteNormalized
import OCaml.Vm.Boot.Startup.ResolveBackByteImage
import OCaml.Vm.Boot.Startup.ResolveBackNextNormalized
import OCaml.Vm.Boot.Startup.ResolveBackNextImage
import OCaml.Vm.Boot.Startup.ResolveBackDoneNormalized
import OCaml.Vm.Boot.Startup.ResolveBackDoneImage
import OCaml.Vm.Boot.Startup.ResolveDotsNormalized
import OCaml.Vm.Boot.Startup.ResolveDotsImage
import OCaml.Vm.Boot.Startup.ResolveSaveNormalized
import OCaml.Vm.Boot.Startup.ResolveSaveImage
import OCaml.Vm.Boot.Startup.ResolveSaveCallInterface
import OCaml.Vm.Boot.Startup.FsInit
import OCaml.Vm.Boot.Startup.NativeWord32
import OCaml.Vm.Boot.Startup.IndexedLoop
import OCaml.Vm.Boot.Startup.NameData
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

/-! htif.c's `resolve(path, r)` for a one-component relative path that names
no file ("ocamlrun"): `fs_init`, the scans of the path, `strchr` and `strlen`,
`child` missing, then `R_NONE`. -/

open Sail in
/-- `auipc a5; lw a5,940(a5)` at 0x8000056c: `fs_ready`. -/
theorem resolve_ready_auipc : 2147485036#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 411543#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 940#12 = BitVec.ofNat 64 Layout.sym_fs_ready := by decide

def resolveSlots (ra s3 s4 s9 : BitVec 64) : List (Nat × BitVec 64) := [(56, s3), (8, s9), (88, ra), (48, s4)]
def resolveLog (sp ra s3 s4 s9 : BitVec 64) : List WEntry := nativeWordLog sp 96 (resolveSlots ra s3 s4 s9)
def resolveInput (sp ra s3 s4 s9 path r : BitVec 64) : GRegs :=
  [(2, sp), (19, s3), (25, s9), (1, ra), (20, s4), (10, path), (11, r)]

theorem resolveLog_inside {sp ra s3 s4 s9} (frame : NativeFrame sp 96) :
    LogInW [⟨nativeFrameBase sp 96, sp.toNat⟩] (resolveLog sp ra s3 s4 s9) := by
  apply frame.word_log_inside
  intro off value member
  simp only [resolveSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

def resolveEntered (sp ra s4 path r : BitVec 64) : GRegs :=
  [(19, r), (25, path), (2, nativeStack sp 96), (15, 0#64), (1, ra), (20, s4), (10, path), (11, r)]

/-- The first `resolve`: `fs_ready` is clear, so save and call `fs_init`. -/
theorem resolve_entry (c : Config) (sp ra s3 s4 s9 path r : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (resolveInput sp ra s3 s4 s9 path r))
    (notReady : read4 c.σ.mem Layout.sym_fs_ready = [0#8, 0#8, 0#8, 0#8]) :
    FnSummary 0x8000056c#64 (fun e => e = c)
      (WriteRegistersPost [19, 25, 2, 15] (resolveLog sp ra s3 s4 s9) c 0x80000594#64 path
        (resolveEntered sp ra s4 path r)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (resolveLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput resolveX056cFSeg 0x8000056c#64 (resolveInput sp ra s3 s4 s9 path r)
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
        · change guardB bop.BNE (bytesVal .lw (read4 c.σ.mem Layout.sym_fs_ready)) 0#64 = false
          rw [notReady]
          decide }))
  · simp only [resolveX056cFSeg, evalBlocks, evalBlock, SegEvalState.init, resolveentry_line_8000056c, resolveentry_line_80000570, resolveentry_line_80000574, resolveentry_line_80000578, resolveentry_line_8000057c, resolveentry_line_80000580, resolveentry_line_80000584, resolveentry_line_80000588, resolveentry_line_8000058c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveInput, imm20Of, resolveLog,
      resolveSlots, nativeWordLog, List.map, List.nil_append, List.cons_append]
    rw [show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide]
    rfl
  · rfl
  · simp only [resolveX056cFSeg, evalBlocks, evalBlock, SegEvalState.init, resolveentry_line_8000056c, resolveentry_line_80000570, resolveentry_line_80000574, resolveentry_line_80000578, resolveentry_line_8000057c, resolveentry_line_80000580, resolveentry_line_80000584, resolveentry_line_80000588, resolveentry_line_8000058c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveInput, imm20Of]
    rw [show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.add_zero, notReady]
    simp only [resolveEntered, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨rfl, by decide⟩
  · rfl
  · decide

/-- `*r`'s address `off` bytes in, inside `_open`'s 80-byte frame. -/
def resAt (spo : BitVec 64) (off : Nat) : Nat := (nativeStack spo 80 + BitVec.ofNat 64 off).toNat

def resolveClearLog (spo : BitVec 64) : List WEntry :=
  [(resAt spo 8, 8, 0#64), (resAt spo 8, 4, -1#64), (resAt spo 0, 8, 0#64), (resAt spo 16, 8, 0#64),
    (resAt spo 24, 8, 0#64), (resAt spo 32, 8, 0#64), (resAt spo 40, 8, 0#64)]

theorem resAt_nat {spo : BitVec 64} (frame : NativeFrame spo 80) {off : Nat} (h : off ≤ 80) :
    resAt spo off = nativeFrameBase spo 80 + off := by
  rw [resAt, nativeStack, frame.address off h, frame.slot_nat h]

theorem resolveClearLog_inside {spo : BitVec 64} (frame : NativeFrame spo 80) :
    LogInW [⟨nativeFrameBase spo 80, spo.toNat⟩] (resolveClearLog spo) := by
  have lower := frame.lower
  simp only [resolveClearLog, LogInW, InsideW, resAt_nat frame (by decide : 8 ≤ 80), resAt_nat frame (by decide : 0 ≤ 80),
    resAt_nat frame (by decide : 16 ≤ 80), resAt_nat frame (by decide : 24 ≤ 80), resAt_nat frame (by decide : 32 ≤ 80),
    resAt_nat frame (by decide : 40 ≤ 80), or_false, and_true]
  unfold nativeFrameBase at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Zero `*r` (in `_open`'s 80-byte frame) and set `r->node = -1`. -/
theorem resolve_clear (c : Config) (spo path ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame spo 80)
    (regs : GHolds c.σ [(19, nativeStack spo 80), (25, path)]) :
    FnSummary 0x80000598#64 (fun e => e = c) (WriteRegistersPost [10, 15] (resolveClearLog spo) c 0x800005bc#64 path
      [(10, path), (15, -1#64), (19, nativeStack spo 80), (25, path)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (resolveClearLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput resolveX0598Seg 0x80000598#64 [(19, nativeStack spo 80), (25, path)]
        [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [19, 25]; decide
      shape := by change ChainOK _ [19, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveClear_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        have half : WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 8) 4 :=
          have w := slot 8 (by decide) (by decide)
          ⟨w.lower, by have := w.upper; omega, w.htif, by have := w.aligned; omega⟩
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact half.sw rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl }))
  · simp only [resolveX0598Seg, evalBlocks, evalBlock, SegEvalState.init, resolveclear_line_80000598, resolveclear_line_8000059c, resolveclear_line_800005a0, resolveclear_line_800005a4, resolveclear_line_800005a8, resolveclear_line_800005ac, resolveclear_line_800005b0, resolveclear_line_800005b4, resolveclear_line_800005b8, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.nil_append,
      resolveClearLog, resAt, show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide, BitVec.zero_add,
      show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide,
      show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, show Functions.sign_extend (m := 64) 40#12 = 40#64 by decide]
  · rfl
  · simp only [resolveX0598Seg, evalBlocks, evalBlock, SegEvalState.init, resolveclear_line_80000598, resolveclear_line_8000059c, resolveclear_line_800005a0, resolveclear_line_800005a4, resolveclear_line_800005a8, resolveclear_line_800005ac, resolveclear_line_800005b0, resolveclear_line_800005b4, resolveclear_line_800005b8, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of,
      show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide, BitVec.zero_add,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]
  · rfl
  · decide

theorem resolve_strlen_call (c : Config) (spo path ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame spo 80)
    (regs : GHolds c.σ [(19, nativeStack spo 80), (25, path)]) :
    FnSummary 0x80000598#64 (fun e => e = c)
      (WriteRegistersPost ([10, 15] ++ [1]) (resolveClearLog spo) c jal_800005bc_call.target path
        ((1, jal_800005bc_call.link) :: [(10, path), (15, -1#64), (19, nativeStack spo 80), (25, path)])) :=
  block_then_call c jal_800005bc_call_shape jal_800005bc_call_decode (fun _ h => jal_800005bc_call_pins h)
    (resolve_clear c spo path ra leaf frame regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

theorem resAt36_window {spo : BitVec 64} (frame : NativeFrame spo 80) :
    WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 36) 4 := by
  have w : WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 32) 8 := by
    rw [nativeStack, frame.address _ (by omega)]
    exact frame.word (by decide) (by decide)
  rw [nativeStack, frame.address _ (by omega)] at w ⊢
  have nat := frame.slot_nat (off := 32) (by omega)
  have nat36 := frame.slot_nat (off := 36) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [nat36]
  · have := w.lower; rw [nat] at this; omega
  · have := w.upper; rw [nat] at this; omega
  · have := w.htif; rw [nat] at this; omega
  · have := w.aligned; rw [nat] at this; omega

/-- `path[len - 1] == '/'` as `seqz` computes it. -/
def slashFlag (b : BitVec 8) : BitVec 64 :=
  compareValue true (bytesVal .lbu [b] + Functions.sign_extend (m := 64) 4049#12) (Functions.sign_extend (m := 64) 1#12)

/-- After `strlen(path) = len`: test the path's last byte for '/'. -/
theorem resolve_flag_test (c : Config) (spo path len ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, len), (19, nativeStack spo 80), (25, path)])
    (nonzero : len ≠ 0#64) (window : ReadWindow (path + len - 1#64) 1)
    (last : (c.σ.mem[(path + len - 1#64).toNat]?).getD 0 = b) :
    FnSummary 0x800005c0#64 (fun e => e = c)
      (WriteRegistersPost [15] [] c 0x800005d8#64 len [(15, slashFlag b), (10, len), (19, nativeStack spo 80), (25, path)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (resolveX05c0FSeg ++ resolveX05c8Seg) 0x800005c0#64
        [(10, len), (19, nativeStack spo 80), (25, path)] [[b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 19, 25]; decide
      shape := by change ChainOK _ [10, 19, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveSlash_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · change guardB bop.BEQ len 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero
        · exact window.lbu rfl (by
            simp only [resolveslash_line_800005c0, resolveslash_line_800005c8, resolveslash_line_800005cc, resolveslash_line_800005d0, resolveslash_line_800005d4, resolveslash_line_800005d8, resolveslash_line_800005dc, resolveslash_line_800005e0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
              ite_true, ite_false, Nat.reduceEqDiff]
            rw [show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide]
            exact (BitVec.sub_eq_add_neg _ _).symm) last }))
  · rfl
  · rfl
  · simp only [resolveX05c0FSeg, resolveX05c8Seg, evalBlocks, evalBlock, SegEvalState.init, resolveslash_line_800005c0, resolveslash_line_800005c8, resolveslash_line_800005cc, resolveslash_line_800005d0, resolveslash_line_800005d4, resolveslash_line_800005d8, resolveslash_line_800005dc, resolveslash_line_800005e0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append,
      List.nil_append]
    rfl
  · rfl
  · decide

/-- Store `r->slash` and start the backward scan from the path's end. -/
theorem resolve_flag_store (c : Config) (spo path len v ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame spo 80) (regs : GHolds c.σ [(15, v), (10, len), (19, nativeStack spo 80), (25, path)]) :
    FnSummary 0x800005d8#64 (fun e => e = c)
      (WriteRegistersPost [15, 12] [(resAt spo 36, 4, v)] c 0x800005f4#64 len
        [(15, len), (12, 47#64), (10, len), (19, nativeStack spo 80), (25, path)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (by
      have lower := frame.lower
      simp only [LogInW, InsideW, resAt_nat frame (by decide : 36 ≤ 80), or_false, and_true]
      unfold nativeFrameBase at *; omega))
    (block_summary _ _ _ _ _ (show BlockInput resolveX05d8Seg 0x800005d8#64
        [(15, v), (10, len), (19, nativeStack spo 80), (25, path)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 10, 19, 25]; decide
      shape := by change ChainOK _ [15, 10, 19, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveSlash_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        exact (resAt36_window frame).sw rfl rfl }))
  · simp only [resolveX05d8Seg, evalBlocks, evalBlock, SegEvalState.init, resolveslash_line_800005c0, resolveslash_line_800005c8, resolveslash_line_800005cc, resolveslash_line_800005d0, resolveslash_line_800005d4, resolveslash_line_800005d8, resolveslash_line_800005dc, resolveslash_line_800005e0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, resAt,
      show Functions.sign_extend (m := 64) 36#12 = 36#64 by decide]
    rfl
  · rfl
  · simp only [resolveX05d8Seg, evalBlocks, evalBlock, SegEvalState.init, resolveslash_line_800005c0, resolveslash_line_800005c8, resolveslash_line_800005cc, resolveslash_line_800005d0, resolveslash_line_800005d4, resolveslash_line_800005d8, resolveslash_line_800005dc, resolveslash_line_800005e0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide,
      BitVec.add_zero, BitVec.zero_add]
  · rfl
  · decide

/-- The last byte is not '/': the trailing-slash scan stops at once and the
scan for the last component starts at the path's end. -/
theorem resolve_back_start (c : Config) (path len ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(15, len), (12, 47#64), (10, len), (25, path)]) (nonzero : len ≠ 0#64)
    (window : ReadWindow (path + len - 1#64) 1) (last : (c.σ.mem[(path + len - 1#64).toNat]?).getD 0 = b)
    (notSlash : b ≠ 47#8) :
    FnSummary 0x800005f4#64 (fun e => e = c) (WriteRegistersPost [14, 13, 11] [] c 0x800007d0#64 len
        [(11, 47#64), (14, len), (13, nameByteWord b), (15, len), (12, 47#64), (10, len), (25, path)]) := by
  have addr : path + (len + Functions.sign_extend (m := 64) 4095#12) + Functions.sign_extend (m := 64) 0#12 =
      path + len - 1#64 := by
    rw [show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, ← BitVec.add_assoc,
      ← BitVec.sub_eq_add_neg]
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (resolveX05f4TSeg ++ resolveX05e8TSeg ++ resolveX07c0Seg) 0x800005f4#64
        [(15, len), (12, 47#64), (10, len), (25, path)] [[b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 12, 10, 25]; decide
      shape := by change ChainOK _ [15, 12, 10, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveEnd_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · change guardB bop.BNE len 0#64 = true
          exact bne_iff_ne.mpr nonzero
        · refine memFacts_writeLog (window.lbu rfl (by
            simp only [resolveend_line_800005f4, resolveend_line_800005f8, resolvelast_line_800005e8, resolvelast_line_800005f0, resolveback_line_800007c0, resolveback_line_800007c4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
              ite_true, ite_false, Nat.reduceEqDiff]
            exact addr) last) (fun _ => by simp only [resolveend_line_800005f4, resolveend_line_800005f8, resolvelast_line_800005e8, resolvelast_line_800005f0, resolveback_line_800007c0, resolveback_line_800007c4, wlogM]; trivial)
        · change guardB bop.BNE (bytesVal .lbu [b]) (0#64 + Functions.sign_extend (m := 64) 47#12) = true
          rw [name_lbu_value, show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide, BitVec.zero_add]
          exact bne_iff_ne.mpr (nameByteWord_ne_of notSlash (by decide)) }))
  · rfl
  · rfl
  · simp only [resolveX05f4TSeg, resolveX05e8TSeg, resolveX07c0Seg, evalBlocks, evalBlock, SegEvalState.init, resolveend_line_800005f4, resolveend_line_800005f8, resolvelast_line_800005e8, resolvelast_line_800005f0, resolveback_line_800007c0, resolveback_line_800007c4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append,
      List.nil_append, name_lbu_value, show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.zero_add, BitVec.add_zero]
  · rfl
  · decide

/-- One step of the scan for the last component: byte `k - 1` is not '/'. -/
theorem resolve_back_step (c : Config) (path k a0 ra : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(14, k), (11, 47#64), (10, a0), (25, path)]) (nonzero : k ≠ 0#64)
    (window : ReadWindow (path + (k - 1#64)) 1) (byte : (c.σ.mem[(path + (k - 1#64)).toNat]?).getD 0 = b)
    (notSlash : b ≠ 47#8) :
    FnSummary 0x800007d0#64 (fun e => e = c) (WriteRegistersPost [13, 12, 14] [] c 0x800007d0#64 a0
        [(14, k - 1#64), (12, nameByteWord b), (13, k - 1#64), (11, 47#64), (10, a0), (25, path)]) := by
  have dec : k + Functions.sign_extend (m := 64) 4095#12 = k - 1#64 := by
    rw [show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide, ← BitVec.sub_eq_add_neg]
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (resolveX07d0FSeg ++ resolveX07dcTSeg ++ resolveX07ccSeg) 0x800007d0#64
        [(14, k), (11, 47#64), (10, a0), (25, path)] [[b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 11, 10, 25]; decide
      shape := by change ChainOK _ [14, 11, 10, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveBackTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · change guardB bop.BEQ k 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero
        · refine memFacts_writeLog (window.lbu rfl (by
            simp only [resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebacknext_line_800007cc, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
              ite_true, ite_false, Nat.reduceEqDiff]
            rw [dec, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) byte)
            (fun _ => by simp only [resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebacknext_line_800007cc, wlogM]; trivial)
        · change guardB bop.BNE (bytesVal .lbu [b]) 47#64 = true
          rw [name_lbu_value]
          exact bne_iff_ne.mpr (nameByteWord_ne_of notSlash (by decide)) }))
  · rfl
  · rfl
  · simp only [resolveX07d0FSeg, resolveX07dcTSeg, resolveX07ccSeg, evalBlocks, evalBlock, SegEvalState.init, resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackbyte_line_800007dc, resolvebacknext_line_800007cc, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append,
      List.nil_append, name_lbu_value, dec, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      BitVec.add_zero]
  · rfl
  · decide

/-- The scan for the last component after `j` steps: `a4 = L - j`. -/
structure BackAt (path : BitVec 64) (L : Nat) (a0 ra : BitVec 64) (start : Config) (j : Nat) (c : Config) : Prop where
  leaf : LeafInput ra c
  bound : j ≤ L
  pc : PCAt 0x800007d0#64 c
  regs : GHolds c.σ [(14, BitVec.ofNat 64 (L - j)), (11, 47#64), (10, a0), (25, path)]
  memory : c.σ.mem = start.σ.mem
  output : c.σ.sailOutput = start.σ.sailOutput
  frame : ∀ r : Register, (∀ n ∈ [13, 12, 14], gprReg n ≠ r) →
    (∀ q ∈ noiseRegs, (q == r) = false) → c.σ.regs.get? r = start.σ.regs.get? r

def backIndex (L : Nat) (c : Config) : Nat := L - ((gprGet c.σ 14).getD 0).toNat

/-- A path of `L` bytes, none '/'. -/
structure NoSlash (m : Std.ExtHashMap Nat (BitVec 8)) (path : BitVec 64) (L : Nat) : Prop where
  region : ReadWindow path (L + 1)
  free : ∀ j, j < L → strByte m (path.toNat + j) ≠ 47#8

theorem back_iteration {path L a0 ra start j c} (run : NoSlash start.σ.mem path L) (h : BackAt path L a0 ra start j c)
    (hj : j < L) : ∃ d, Steps c d ∧ BackAt path L a0 ra start (j + 1) d := by
  have small : L < 2 ^ 64 := by have := run.region.upper; omega
  have kNe : BitVec.ofNat 64 (L - j) ≠ 0#64 := by
    intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  have kDec : BitVec.ofNat 64 (L - j) - 1#64 = BitVec.ofNat 64 (L - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : L - j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : L - (j + 1) < 2 ^ 64)]
    omega
  have cursor : path + (BitVec.ofNat 64 (L - j) - 1#64) = nameCursor path (L - (j + 1)) := by
    rw [kDec]; rfl
  have nat := nameCursor_nat run.region (k := L - (j + 1)) (by omega)
  obtain ⟨d, run1, post⟩ := (resolve_back_step c path _ a0 ra (strByte start.σ.mem (path.toNat + (L - (j + 1))))
    h.leaf h.regs kNe (by rw [cursor]; exact name_window run.region (by omega))
    (by rw [cursor, nat, h.memory]; rfl) (run.free _ (by omega))).run c ⟨h.pc, rfl⟩
  refine ⟨d, run1, {
    leaf := ⟨post.good, post.image, post.minstret,
      (post.frame .x1 (by decide) (by decide)).trans h.leaf.raReg, h.leaf.aligned, post.tick⟩
    bound := by omega
    pc := post.pc
    regs := ?_
    memory := post.memory.trans h.memory
    output := post.output.trans h.output
    frame := fun r outside noise => (post.frame r (fun n hn => outside n (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; omega)) noise).trans (h.frame r outside noise) }⟩
  rw [← kDec]
  exact ⟨gholds_lookup (n := 14) _ post.regs (by rfl), gholds_lookup (n := 11) _ post.regs (by rfl),
    gholds_lookup (n := 10) _ post.regs (by rfl), gholds_lookup (n := 25) _ post.regs (by rfl), trivial⟩

theorem BackAt.index {path L a0 ra start j c} (small : L < 2 ^ 64) (h : BackAt path L a0 ra start j c) :
    backIndex L c = j := by
  simp only [backIndex, gholds_lookup (n := 14) _ h.regs (by rfl), Option.getD_some, BitVec.toNat_ofNat]
  have := h.bound
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The whole scan for the last component over a '/'-free path. -/
theorem back_loop {path L a0 ra} (start : Config) (run : NoSlash start.σ.mem path L) :
    Triple (BackAt path L a0 ra start 0) (BackAt path L a0 ra start L) :=
  indexed_loop (backIndex L) L 0 _ (fun _ _ h => h.bound)
    (fun _ _ h => h.index (by have := run.region.upper; omega)) (fun _ _ h hj => back_iteration run h hj)

/-- The last component is the whole path (`b = 0`), neither "." nor "..":
clear `r->last_dotdot`, start at the root. -/
theorem resolve_back_exit (c : Config) (spo path len ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame spo 80)
    (regs : GHolds c.σ [(14, 0#64), (15, len), (10, len), (25, path), (19, nativeStack spo 80)])
    (nonzero : len ≠ 0#64) (notOne : len ≠ 1#64) (notTwo : len ≠ 2#64) :
    FnSummary 0x800007d0#64 (fun e => e = c) (WriteRegistersPost [20, 15, 13, 12] [(resAt spo 44, 4, 0#64)] c 0x8000062c#64 len
      [(20, 0#64), (15, 0#64), (13, 2#64), (12, path - 1#64), (14, 0#64), (10, len), (25, path),
        (19, nativeStack spo 80)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (by
      have lower := frame.lower
      simp only [LogInW, InsideW, resAt_nat frame (by decide : 44 ≤ 80), or_false, and_true]
      unfold nativeFrameBase at *; omega))
    (block_summary _ _ _ _ _ (show BlockInput (resolveX07d0TSeg ++ resolveX07e4TSeg ++ resolveX0604TSeg ++
        resolveX061cFSeg) 0x800007d0#64 [(14, 0#64), (15, len), (10, len), (25, path), (19, nativeStack spo 80)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [14, 15, 10, 25, 19]; decide
      shape := by change ChainOK _ [14, 15, 10, 25, 19] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveBackTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · change guardB bop.BEQ 0#64 0#64 = true
          decide
        · change guardB bop.BNE (len - 0#64) (0#64 + Functions.sign_extend (m := 64) 1#12) = true
          rw [BitVec.sub_zero, show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, BitVec.zero_add]
          exact bne_iff_ne.mpr notOne
        · change guardB bop.BNE (len - 0#64) (0#64 + Functions.sign_extend (m := 64) 2#12) = true
          rw [BitVec.sub_zero, show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide, BitVec.zero_add]
          exact bne_iff_ne.mpr notTwo
        · exact (show WriteWindow (nativeStack spo 80 + BitVec.ofNat 64 44) 4 by
            rw [nativeStack, frame.address 44 (by decide)]; exact frame.word32 (by decide) (by decide)).sw rfl (by
            simp only [resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
              ite_false, Nat.reduceEqDiff]
            rw [show Functions.sign_extend (m := 64) 44#12 = 44#64 by decide])
        · change guardB bop.BEQ len 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · simp only [resolveX07d0TSeg, resolveX07e4TSeg, resolveX0604TSeg, resolveX061cFSeg, evalBlocks, evalBlock,
      SegEvalState.init, resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      imm20Of, List.cons_append, List.nil_append, resAt, show Functions.sign_extend (m := 64) 44#12 = 44#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.zero_add]
  · rfl
  · simp only [resolveX07d0TSeg, resolveX07e4TSeg, resolveX0604TSeg, resolveX061cFSeg, evalBlocks, evalBlock,
      SegEvalState.init, resolvebacktest_line_800007d0, resolvebacktest_line_800007d4, resolvebackdone_line_800007e4, resolvebackdone_line_800007e8, resolvedots_line_80000604, resolvedots_line_8000060c, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      imm20Of, List.cons_append, List.nil_append, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide,
      show Functions.sign_extend (m := 64) 4095#12 = -1#64 by decide, BitVec.zero_add]
    rw [← BitVec.sub_eq_add_neg]
  · rfl
  · decide

open Sail in
/-- `auipc s6; addi s6,s6,-400` at 0x80000658: the `files` table. -/
theorem resolve_files_auipc : 2147485272#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 416535#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 3696#12 = BitVec.ofNat 64 Layout.sym_files := by decide

def resolveLoopSlots (s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64) : List (Nat × BitVec 64) :=
  [(64, s2), (40, s5), (32, s6), (24, s7), (16, s8), (80, s0), (72, s1), (0, s10)]
def resolveLoopLog (sp s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64) : List WEntry :=
  nativeWordLog sp 96 (resolveLoopSlots s0 s1 s2 s5 s6 s7 s8 s10)
def resolveLoopInput (sp path s0 s1 s2 s5 s6 s7 s8 s10 : BitVec 64) : GRegs :=
  [(2, nativeStack sp 96), (25, path), (18, s2), (21, s5), (22, s6), (23, s7), (24, s8), (8, s0), (9, s1), (26, s10)]

def resolveLooped (sp path s0 s1 s10 : BitVec 64) : GRegs :=
  [(21, 1#64), (24, 46#64), (23, 2#64), (22, BitVec.ofNat 64 Layout.sym_files), (18, 47#64), (10, path), (11, 47#64),
    (2, nativeStack sp 96), (25, path), (8, s0), (9, s1), (26, s10)]

/-- Save the loop's registers and call `strchr(path, '/')`. -/
theorem resolve_loop_save (c : Config) (sp path s0 s1 s2 s5 s6 s7 s8 s10 ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (resolveLoopInput sp path s0 s1 s2 s5 s6 s7 s8 s10)) :
    FnSummary 0x8000062c#64 (fun e => e = c)
      (WriteRegistersPost [21, 24, 23, 22, 18, 10, 11] (resolveLoopLog sp s0 s1 s2 s5 s6 s7 s8 s10) c 0x8000066c#64 path
        (resolveLooped sp path s0 s1 s10)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (frame.word_log_inside fun off value member => by
      simp only [resolveLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega))
    (block_summary _ _ _ _ _ (show BlockInput resolveX062cSeg 0x8000062c#64
        (resolveLoopInput sp path s0 s1 s2 s5 s6 s7 s8 s10) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 25, 18, 21, 22, 23, 24, 8, 9, 26]; decide
      shape := by change ChainOK _ [2, 25, 18, 21, 22, 23, 24, 8, 9, 26] _; decide
      tick := leaf.tick
      facts := by
        have code := resolveSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 96) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 96 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.resolve_at_"
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 80 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl }))
  · simp only [resolveX062cSeg, evalBlocks, evalBlock, SegEvalState.init, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveLoopInput, imm20Of,
      resolveLoopLog, resolveLoopSlots, nativeWordLog, List.map, List.nil_append, show Functions.sign_extend (m := 64) 64#12 = BitVec.ofNat 64 64 by decide, show Functions.sign_extend (m := 64) 40#12 = BitVec.ofNat 64 40 by decide, show Functions.sign_extend (m := 64) 32#12 = BitVec.ofNat 64 32 by decide, show Functions.sign_extend (m := 64) 24#12 = BitVec.ofNat 64 24 by decide, show Functions.sign_extend (m := 64) 16#12 = BitVec.ofNat 64 16 by decide, show Functions.sign_extend (m := 64) 80#12 = BitVec.ofNat 64 80 by decide, show Functions.sign_extend (m := 64) 72#12 = BitVec.ofNat 64 72 by decide, show Functions.sign_extend (m := 64) 0#12 = BitVec.ofNat 64 0 by decide]
  · rfl
  · simp only [resolveX062cSeg, evalBlocks, evalBlock, SegEvalState.init, resolvesave_line_8000061c, resolvesave_line_80000620, resolvesave_line_80000624, resolvesave_line_8000062c, resolvesave_line_80000630, resolvesave_line_80000634, resolvesave_line_80000638, resolvesave_line_8000063c, resolvesave_line_80000640, resolvesave_line_80000644, resolvesave_line_80000648, resolvesave_line_8000064c, resolvesave_line_80000650, resolvesave_line_80000654, resolvesave_line_80000658, resolvesave_line_8000065c, resolvesave_line_80000660, resolvesave_line_80000664, resolvesave_line_80000668, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, resolveLoopInput, imm20Of,
      resolve_files_auipc, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide,
      show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide, show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide,
      show Functions.sign_extend (m := 64) 46#12 = 46#64 by decide,
      show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide, BitVec.zero_add, BitVec.add_zero, resolveLooped]
  · rfl
  · decide

theorem resolve_strchr_call (c : Config) (sp path s0 s1 s2 s5 s6 s7 s8 s10 ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (resolveLoopInput sp path s0 s1 s2 s5 s6 s7 s8 s10)) :
    FnSummary 0x8000062c#64 (fun e => e = c)
      (WriteRegistersPost ([21, 24, 23, 22, 18, 10, 11] ++ [1]) (resolveLoopLog sp s0 s1 s2 s5 s6 s7 s8 s10) c
        jal_8000066c_call.target path ((1, jal_8000066c_call.link) :: resolveLooped sp path s0 s1 s10)) :=
  block_then_call c jal_8000066c_call_shape jal_8000066c_call_decode (fun _ h => jal_8000066c_call_pins h)
    (resolve_loop_save c sp path s0 s1 s2 s5 s6 s7 s8 s10 ra leaf frame regs)
    (by simp only [resolveLooped, keysG]; decide) (by simp only [resolveLooped, KeysAvoidRa, keysG]; decide) rfl
end OCaml.Vm.Boot.Startup
