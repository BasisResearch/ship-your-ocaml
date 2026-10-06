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
import OCaml.Vm.Boot.Startup.FsInit
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives LeanRV64DExecutable

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
end OCaml.Vm.Boot.Startup
