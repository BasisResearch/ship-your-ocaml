import OCaml.Vm.Boot.Startup.LibOpenEntryNormalized
import OCaml.Vm.Boot.Startup.LibOpenEntryImage
import OCaml.Vm.Boot.Startup.LibOpenEntryCallInterface
import OCaml.Vm.Boot.Startup.ResolveRun
import OCaml.Vm.Boot.Startup.OpenRCheckNormalized
import OCaml.Vm.Boot.Startup.OpenRCheckImage
import OCaml.Vm.Boot.Startup.OpenRErrnoNormalized
import OCaml.Vm.Boot.Startup.OpenRErrnoImage
import OCaml.Vm.Boot.Startup.OpenRReturnNormalized
import OCaml.Vm.Boot.Startup.OpenRReturnImage
import OCaml.Vm.Boot.Startup.OpenRStoreNormalized
import OCaml.Vm.Boot.Startup.OpenRStoreImage
import OCaml.Vm.Boot.Startup.LibOpenReturnNormalized
import OCaml.Vm.Boot.Startup.LibOpenReturnImage
import OCaml.Vm.Boot.Startup.ErrnoNormalized
import OCaml.Vm.Boot.Startup.ErrnoImage
import OCaml.Vm.Boot.Startup.HtifOpenErrnoSetNormalized
import OCaml.Vm.Boot.Startup.HtifOpenErrnoSetImage
import OCaml.Vm.Boot.Startup.HtifOpenReturnNormalized
import OCaml.Vm.Boot.Startup.HtifOpenReturnImage
import OCaml.Vm.Boot.Startup.HtifOpenKindNormalized
import OCaml.Vm.Boot.Startup.HtifOpenKindImage
import OCaml.Vm.Boot.Startup.HtifOpenNoneNormalized
import OCaml.Vm.Boot.Startup.HtifOpenNoneImage
import OCaml.Vm.Boot.Startup.HtifOpenEnoentNormalized
import OCaml.Vm.Boot.Startup.HtifOpenEnoentImage
import OCaml.Vm.Boot.Startup.HtifOpenErrnoCallNormalized
import OCaml.Vm.Boot.Startup.HtifOpenErrnoCallImage
import OCaml.Vm.Boot.Startup.HtifOpenErrnoCallCallInterface
import OCaml.Vm.Boot.Startup.HtifOpenEntryNormalized
import OCaml.Vm.Boot.Startup.HtifOpenEntryImage
import OCaml.Vm.Boot.Startup.HtifOpenEntryCallInterface
import OCaml.Vm.Boot.Startup.OpenREntryNormalized
import OCaml.Vm.Boot.Startup.OpenREntryImage
import OCaml.Vm.Boot.Startup.OpenREntryCallInterface
import OCaml.Vm.Boot.Startup.RuntimeErrno
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Logic Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
  LeanRV64DExecutable

/-! `open(path, flags, …)` → `_open_r(reent, path, flags, mode)` → `_open` for a
path that names no file: ENOENT, -1. -/

open Sail in
/-- `auipc a0; ld a0,868(a0)` at 0x80042594: `_impure_ptr`. -/
theorem open_impure_auipc : 2147755412#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 140567#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 868#12 = BitVec.ofNat 64 allocatorImpureAddr := by decide

/-- A block followed by its direct call, keeping only a selected register
list across the call (the block may read and save `ra`). -/
theorem block_then_call_select {entry : BitVec 64} {writes : List Nat} {log : List WEntry} {value : BitVec 64}
    {regs : GRegs} {a : CallInstr} (c : Config) (shape : CallShape a) (decode : CallDecode a)
    (pins : ∀ d : Config, ExecutableImage d → CallPins a d)
    (front : FnSummary entry (fun d => d = c) (WriteRegistersPost writes log c a.pc value regs))
    (kept : GRegs) (select : ∀ n v, (n, v) ∈ kept → lookupG n regs = some v)
    (keys : KeysOK (keysG kept)) (avoid : KeysAvoidRa kept) (result : lookupG 10 kept = some value) :
    FnSummary entry (fun d => d = c)
      (WriteRegistersPost (writes ++ [1]) log c a.target value ((1, a.link) :: kept)) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary shape decode request (pins _ setup.image) setup.good
    setup.image setup.tick setup.minstret kept (gholds_select setup.regs kept select) keys avoid result).run request
    ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩

def libOpenSlots (sp ra a2 a3 a4 a5 a6 a7 : BitVec 64) : List (Nat × BitVec 64) :=
  [(32, a2), (40, a3), (24, ra), (48, a4), (56, a5), (64, a6), (72, a7), (8, nativeStack sp 80 + 32#64)]
def libOpenLog (sp ra a2 a3 a4 a5 a6 a7 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 (libOpenSlots sp ra a2 a3 a4 a5 a6 a7)
def libOpenInput (sp ra path flags a2 a3 a4 a5 a6 a7 : BitVec 64) : GRegs :=
  [(2, sp), (1, ra), (10, path), (11, flags), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6), (17, a7)]

def libOpened (sp ra path flags a2 a4 a5 a6 a7 reent : BitVec 64) : GRegs :=
  [(12, flags), (11, path), (13, Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb a2 31 0)),
    (6, nativeStack sp 80 + 32#64), (28, flags), (2, nativeStack sp 80), (10, reent), (29, path), (1, ra), (14, a4),
    (15, a5), (16, a6), (17, a7)]

/-- `open`: spill the variadic arguments and call `_open_r`. -/
theorem lib_open_entry (c : Config) (sp ra path flags a2 a3 a4 a5 a6 a7 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (libOpenInput sp ra path flags a2 a3 a4 a5 a6 a7)) :
    FnSummary 0x80042590#64 (fun e => e = c)
      (WriteRegistersPost [12, 11, 13, 6, 28, 2, 10, 29] (libOpenLog sp ra a2 a3 a4 a5 a6 a7) c 0x800425d4#64
        (getenvReent c) (libOpened sp ra path flags a2 a4 a5 a6 a7 (getenvReent c))) := by
  apply registers_of_blocks leaf.image (frame.image_outside (frame.word_log_inside fun off value member => by
      simp only [libOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      omega))
    (block_summary _ _ _ _ _ (show BlockInput openX2590Seg 0x80042590#64 (libOpenInput sp ra path flags a2 a3 a4 a5 a6 a7)
        [read8 c.σ.mem allocatorImpureAddr] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 10, 11, 12, 13, 14, 15, 16, 17]; decide
      shape := by change ChainOK _ [2, 1, 10, 11, 12, 13, 14, 15, 16, 17] _; decide
      tick := leaf.tick
      facts := by
        have code := libOpenEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.open_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 by constructor <;> decide).ld rfl
            (by simp only [libopenentry_line_80042590, libopenentry_line_80042594, libopenentry_line_80042598, libopenentry_line_8004259c, libopenentry_line_800425a0, libopenentry_line_800425a4, libopenentry_line_800425a8, libopenentry_line_800425ac, libopenentry_line_800425b0, libopenentry_line_800425b4, libopenentry_line_800425b8, libopenentry_line_800425bc, libopenentry_line_800425c0, libopenentry_line_800425c4, libopenentry_line_800425c8, libopenentry_line_800425cc, libopenentry_line_800425d0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, imm20Of, Nat.reduceEqDiff]
                exact open_impure_auipc) (read8_pins _ _)
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · simp only [openX2590Seg, evalBlocks, evalBlock, SegEvalState.init, libopenentry_line_80042590, libopenentry_line_80042594, libopenentry_line_80042598, libopenentry_line_8004259c, libopenentry_line_800425a0, libopenentry_line_800425a4, libopenentry_line_800425a8, libopenentry_line_800425ac, libopenentry_line_800425b0, libopenentry_line_800425b4, libopenentry_line_800425b8, libopenentry_line_800425bc, libopenentry_line_800425c0, libopenentry_line_800425c4, libopenentry_line_800425c8, libopenentry_line_800425cc, libopenentry_line_800425d0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, libOpenInput, imm20Of, libOpenLog,
      libOpenSlots, nativeWordLog, List.map, List.nil_append, List.cons_append,
      show Functions.sign_extend (m := 64) 4016#12 = -BitVec.ofNat 64 80 by decide, show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide, show Functions.sign_extend (m := 64) 40#12 = 40#64 by decide, show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
    rfl
  · rfl
  · simp only [openX2590Seg, evalBlocks, evalBlock, SegEvalState.init, libopenentry_line_80042590, libopenentry_line_80042594, libopenentry_line_80042598, libopenentry_line_8004259c, libopenentry_line_800425a0, libopenentry_line_800425a4, libopenentry_line_800425a8, libopenentry_line_800425ac, libopenentry_line_800425b0, libopenentry_line_800425b4, libopenentry_line_800425b8, libopenentry_line_800425bc, libopenentry_line_800425c0, libopenentry_line_800425c4, libopenentry_line_800425c8, libopenentry_line_800425cc, libopenentry_line_800425d0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, libOpenInput, imm20Of,
      show Functions.sign_extend (m := 64) 4016#12 = -BitVec.ofNat 64 80 by decide, show Functions.sign_extend (m := 64) 32#12 = 32#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, libOpened, getenvReent, read8_value]
    rfl
  · rfl
  · decide

open Sail in
/-- `auipc a5; sw zero,1412(a5)` at 0x8004d7c4: the global `errno`. -/
theorem open_r_errno_auipc : 2147801028#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 96151#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1412#12 = BitVec.ofNat 64 0x80064d48 := by decide

open Sail in
theorem open_r_a5_auipc : 2147801028#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 96151#32 +++ 0#12) =
    0x800647c4#64 := by decide

def openRLog (sp ra s0 : BitVec 64) : List WEntry := nativeWordLog sp 16 [(0, s0), (8, ra)] ++ [(0x80064d48, 4, 0#64)]
def openRInput (sp ra s0 reent path flags mode : BitVec 64) : GRegs :=
  [(2, sp), (1, ra), (8, s0), (10, reent), (11, path), (12, flags), (13, mode)]

/-- `_open_r`: save, clear the global `errno`, call `_open(path, flags, mode)`. -/
theorem open_r_entry (c : Config) (sp ra s0 reent path flags mode : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ (openRInput sp ra s0 reent path flags mode)) :
    FnSummary 0x8004d7a4#64 (fun e => e = c) (WriteRegistersPost [15, 10, 12, 8, 11, 2] (openRLog sp ra s0) c 0x8004d7cc#64 path
      [(15, 0x800647c4#64), (10, path), (12, mode), (8, reent), (11, flags), (2, nativeStack sp 16), (1, ra),
        (13, mode)]) := by
  apply registers_of_blocks leaf.image (imageOutside_append (frame.image_outside (frame.word_log_inside
      fun off value member => by simp at member; omega)) (by constructor <;> simp only [OutLRange] <;> decide))
    (block_summary _ _ _ _ _ (show BlockInput open_rXd7a4Seg 0x8004d7a4#64 (openRInput sp ra s0 reent path flags mode)
        [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 10, 11, 12, 13]; decide
      shape := by change ChainOK _ [2, 1, 8, 10, 11, 12, 13] _; decide
      tick := leaf.tick
      facts := by
        have code := openREntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 16) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 16 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code._open_r_at_"
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064d48) 4 by constructor <;> decide).sw rfl
            (by simp only [openrentry_line_8004d7a4, openrentry_line_8004d7a8, openrentry_line_8004d7ac, openrentry_line_8004d7b0, openrentry_line_8004d7b4, openrentry_line_8004d7b8, openrentry_line_8004d7bc, openrentry_line_8004d7c0, openrentry_line_8004d7c4, openrentry_line_8004d7c8, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact open_r_errno_auipc) }))
  · simp only [open_rXd7a4Seg, evalBlocks, evalBlock, SegEvalState.init, openrentry_line_8004d7a4, openrentry_line_8004d7a8, openrentry_line_8004d7ac, openrentry_line_8004d7b0, openrentry_line_8004d7b4, openrentry_line_8004d7b8, openrentry_line_8004d7bc, openrentry_line_8004d7c0, openrentry_line_8004d7c4, openrentry_line_8004d7c8, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of, openRLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append, open_r_errno_auipc,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide]
    rfl
  · rfl
  · simp only [open_rXd7a4Seg, evalBlocks, evalBlock, SegEvalState.init, openrentry_line_8004d7a4, openrentry_line_8004d7a8, openrentry_line_8004d7ac, openrentry_line_8004d7b0, openrentry_line_8004d7b4, openrentry_line_8004d7b8, openrentry_line_8004d7bc, openrentry_line_8004d7c0, openrentry_line_8004d7c4, openrentry_line_8004d7c8, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRInput, imm20Of,
      show Functions.sign_extend (m := 64) 4080#12 = -BitVec.ofNat 64 16 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, open_r_a5_auipc]
    rfl
  · rfl
  · decide

open Sail in
/-- `lui a5,0x200; addi a5,a5,512`: `O_CREAT | O_DIRECTORY`. -/
theorem open_creat_dir : Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 2099127#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 512#12 = 0x200200#64 := by decide

theorem open_mode_mask : (0#64 &&& Functions.sign_extend (m := 64) 3#12) = 0#64 := by decide

theorem open_flags_none : (0#64 &&& 0x200200#64) = 0#64 := by decide

theorem open_two : (0#64 + Functions.sign_extend (m := 64) 2#12) = 2#64 := by decide

theorem open_mode_ok : guardB bop.BLTU 2#64 0#64 = false := by decide

theorem open_creat_ok : guardB bop.BEQ 0#64 0x200200#64 = false := by decide

def htifOpenSlots (ra s0 s1 s2 : BitVec 64) : List (Nat × BitVec 64) := [(56, s1), (48, s2), (72, ra), (64, s0)]
def htifOpenLog (sp ra s0 s1 s2 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 [(56, s1), (48, s2), (72, ra)] ++ nativeWordLog sp 80 [(64, s0)] ++
    [(resAt sp 4, 4, 0#64), (resAt sp 36, 4, 0#64)]
def htifOpenInput (sp ra s0 s1 s2 path : BitVec 64) : GRegs :=
  [(2, sp), (1, ra), (8, s0), (9, s1), (18, s2), (10, path), (11, 0#64)]

/-- `_open(path, O_RDONLY, ·)`: save, check the flags, call `resolve(path, &r)`. -/
theorem htif_open_entry (c : Config) (sp ra s0 s1 s2 path : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (htifOpenInput sp ra s0 s1 s2 path)) :
    FnSummary 0x800008b8#64 (fun e => e = c) (WriteRegistersPost [11, 8, 14, 15, 9, 18, 2] (htifOpenLog sp ra s0 s1 s2) c 0x800008f8#64 path
      [(11, nativeStack sp 80), (8, 0#64), (14, 0#64), (15, 0x200200#64), (9, 2#64), (18, 0#64), (2, nativeStack sp 80),
        (1, ra), (10, path)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (OCaml.Vm.Sim.logInW_append'
      (OCaml.Vm.Sim.logInW_append' (frame.word_log_inside fun off value member => by simp at member; omega)
        (frame.word_log_inside fun off value member => by simp at member; omega)) (by
      have lower := frame.lower
      simp only [LogInW, InsideW, resAt_nat frame (by decide : 4 ≤ 80), resAt_nat frame (by decide : 36 ≤ 80),
        or_false, and_true]
      unfold nativeFrameBase at *
      refine ⟨?_, ?_⟩ <;> omega)))
    (block_summary _ _ _ _ _ (show BlockInput (openX08b8FSeg ++ openX08d4FSeg ++ openX08ecSeg) 0x800008b8#64
        (htifOpenInput sp ra s0 s1 s2 path) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 8, 9, 18, 10, 11]; decide
      shape := by change ChainOK _ [2, 1, 8, 9, 18, 10, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenEntry_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        have half (off : Nat) (bound : off + 4 ≤ 80) (aligned : off % 4 = 0) :
            WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 4 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word32 bound aligned
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BLTU (0#64 + Functions.sign_extend (m := 64) 2#12)
            (0#64 &&& Functions.sign_extend (m := 64) 3#12) = false
          rw [open_two, open_mode_mask]
          exact open_mode_ok
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BEQ (0#64 &&& (Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 2099127#32 +++ 0#12) +
            Functions.sign_extend (m := 64) 512#12)) (Functions.sign_extend (m := 64)
            (BitVec.extractLsb' 12 20 2099127#32 +++ 0#12) + Functions.sign_extend (m := 64) 512#12) = false
          rw [open_creat_dir, open_flags_none]
          exact open_creat_ok
        · exact (half 4 (by decide) (by decide)).sw rfl rfl
        · exact (half 36 (by decide) (by decide)).sw rfl rfl }))
  · simp only [openX08b8FSeg, openX08d4FSeg, openX08ecSeg, evalBlocks, evalBlock, SegEvalState.init, htifopenentry_line_800008b8, htifopenentry_line_800008bc, htifopenentry_line_800008c0, htifopenentry_line_800008c4, htifopenentry_line_800008c8, htifopenentry_line_800008cc, htifopenentry_line_800008d4, htifopenentry_line_800008d8, htifopenentry_line_800008dc, htifopenentry_line_800008e0, htifopenentry_line_800008e4, htifopenentry_line_800008ec, htifopenentry_line_800008f0, htifopenentry_line_800008f4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, htifOpenInput, imm20Of, htifOpenLog,
      nativeWordLog, List.map, List.nil_append, List.cons_append, resAt,
      show Functions.sign_extend (m := 64) 4016#12 = -BitVec.ofNat 64 80 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 4#12 = 4#64 by decide, show Functions.sign_extend (m := 64) 36#12 = 36#64 by decide]
    rfl
  · rfl
  · simp only [openX08b8FSeg, openX08d4FSeg, openX08ecSeg, evalBlocks, evalBlock, SegEvalState.init, htifopenentry_line_800008b8, htifopenentry_line_800008bc, htifopenentry_line_800008c0, htifopenentry_line_800008c4, htifopenentry_line_800008c8, htifopenentry_line_800008cc, htifopenentry_line_800008d4, htifopenentry_line_800008d8, htifopenentry_line_800008dc, htifopenentry_line_800008e0, htifopenentry_line_800008e4, htifopenentry_line_800008ec, htifopenentry_line_800008f0, htifopenentry_line_800008f4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, htifOpenInput, imm20Of, List.cons_append,
      List.nil_append, show Functions.sign_extend (m := 64) 4016#12 = -BitVec.ofNat 64 80 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add,
      show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide,
      open_mode_mask, open_creat_dir, open_flags_none]
    rfl
  · rfl
  · decide

theorem open_se0 : Functions.sign_extend (m := 64) 0#12 = 0#64 := by decide

theorem kind_none_value : bytesVal .lw [2#8, 0#8, 0#8, 0#8] = 2#64 := by decide

theorem kind_not_err : guardB bop.BEQ 2#64 (0#64 + Functions.sign_extend (m := 64) 3#12) = false := by decide

theorem kind_is_none : guardB bop.BEQ 2#64 2#64 = true := by decide

theorem no_creat : guardB bop.BEQ (0#64 &&& Functions.sign_extend (m := 64) 512#12) 0#64 = true := by decide

/-- After `resolve`: `R_NONE` without `O_CREAT` is ENOENT. -/
theorem htif_open_enoent (c : Config) (sp a0 : BitVec 64) (slash : List (BitVec 8)) (ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ [(2, nativeStack sp 80), (8, 0#64), (9, 2#64), (10, a0)])
    (kind : read4 c.σ.mem (resAt sp 0) = [2#8, 0#8, 0#8, 0#8]) (slashWord : read4 c.σ.mem (resAt sp 36) = slash) :
    FnSummary 0x800008fc#64 (fun e => e = c) (WriteRegistersPost [9, 14, 15, 13, 11] [] c 0x80000944#64 a0
      [(9, 2#64), (14, 0#64), (15, 0#64), (13, bytesVal .lw slash), (11, 2#64), (2, nativeStack sp 80), (8, 0#64),
        (10, a0)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (openX08fcFSeg ++ openX0908TSeg ++ openX0958TSeg ++ openX0b08Seg)
        0x800008fc#64 [(2, nativeStack sp 80), (8, 0#64), (9, 2#64), (10, a0)] [[2#8, 0#8, 0#8, 0#8], slash] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8, 9, 10]; decide
      shape := by change ChainOK _ [2, 8, 9, 10] _; decide
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
        · change guardB bop.BEQ (bytesVal .lw [2#8, 0#8, 0#8, 0#8]) (0#64 + Functions.sign_extend (m := 64) 3#12) = false
          rw [kind_none_value]; exact kind_not_err
        · refine memFacts_writeLog ((word 36 (by decide) (by decide)).lw rfl rfl (by rw [← slashWord]; exact read4_pins _ _))
            (fun _ => by simp only [htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopenenoent_line_80000b08, wlogM]; trivial)
        · change guardB bop.BEQ (bytesVal .lw [2#8, 0#8, 0#8, 0#8]) 2#64 = true
          rw [kind_none_value]; exact kind_is_none
        · change guardB bop.BEQ (0#64 &&& Functions.sign_extend (m := 64) 512#12) 0#64 = true
          exact no_creat }))
  · rfl
  · rfl
  · simp only [openX08fcFSeg, openX0908TSeg, openX0958TSeg, openX0b08Seg, evalBlocks, evalBlock, SegEvalState.init,
      htifopenkind_line_800008fc, htifopenkind_line_80000900, htifopenkind_line_80000908, htifopenkind_line_8000090c, htifopenkind_line_80000910, htifopenkind_line_80000914, htifopenenoent_line_80000b08, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM,
      List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of,
      List.cons_append, List.nil_append, kind_none_value, BitVec.zero_and, open_se0, BitVec.add_zero]
  · rfl
  · decide

theorem htif_open_errno_call (c : Config) (sp a0 : BitVec 64) (slash : List (BitVec 8)) (ra : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ [(2, nativeStack sp 80), (8, 0#64), (9, 2#64), (10, a0)])
    (kind : read4 c.σ.mem (resAt sp 0) = [2#8, 0#8, 0#8, 0#8]) (slashWord : read4 c.σ.mem (resAt sp 36) = slash) :
    FnSummary 0x800008fc#64 (fun e => e = c)
      (WriteRegistersPost ([9, 14, 15, 13, 11] ++ [1]) [] c jal_80000944_call.target a0
        ((1, jal_80000944_call.link) :: [(9, 2#64), (14, 0#64), (15, 0#64), (13, bytesVal .lw slash), (11, 2#64),
          (2, nativeStack sp 80), (8, 0#64), (10, a0)])) :=
  block_then_call c jal_80000944_call_shape jal_80000944_call_decode (fun _ h => jal_80000944_call_pins h)
    (htif_open_enoent c sp a0 slash ra leaf frame regs kind slashWord) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

open Sail in
/-- `auipc a0; ld a0,992(a0)` at 0x80042518: `_impure_ptr`. -/
theorem errno_impure_auipc : 2147755288#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 140567#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 992#12 = BitVec.ofNat 64 allocatorImpureAddr := by decide

/-- `__errno()` returns `_impure_ptr`. -/
theorem errno_return (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c) (regs : GHolds c.σ [(1, ra)]) :
    FnSummary 0x80042518#64 (fun e => e = c)
      (WriteRegistersPost [10] [] c ra (getenvReent c) [(10, getenvReent c), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput errnoX2518Seg 0x80042518#64 [(1, ra)]
        [read8 c.σ.mem allocatorImpureAddr] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [1]; decide
      shape := by change ChainOK _ [1] _; decide
      tick := leaf.tick
      facts := by
        have code := errno_code leaf.image
        chain_facts code with "Vsa.Sim.Code.__errno_at_"
        · exact (show ReadWindow (BitVec.ofNat 64 allocatorImpureAddr) 8 by constructor <;> decide).ld rfl
            (by simp only [errno_line_80042518, errno_line_8004251c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, imm20Of, Nat.reduceEqDiff]
                exact errno_impure_auipc) (read8_pins _ _)
        · change (Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [ret_tgt ra leaf.aligned]
          exact leaf.aligned }))
  · rfl
  · change Sail.BitVec.update (ra + Functions.sign_extend (m := 64) 0#12) 0 0#1 = ra
    rw [ret_tgt ra leaf.aligned]
  · simp only [errnoX2518Seg, evalBlocks, evalBlock, SegEvalState.init, errno_line_80042518, errno_line_8004251c, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, read8_value, getenvReent]
  · rfl
  · decide

def htifOpenRestoreLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [64, 72, 48, 56].map fun off => read8 m (nativeFrameBase sp 80 + off)

/-- `*__errno() = ENOENT`; restore and return -1. -/
theorem htif_open_fail (c : Config) (sp ra s0 s1 s2 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 80)
    (regs : GHolds c.σ [(10, 0x80064668#64), (9, 2#64), (2, nativeStack sp 80)])
    (saved : ∀ off value, (off, value) ∈ [(64, s0), (72, ra), (48, s2), (56, s1)] →
      bytesT c.σ.mem (nativeFrameBase sp 80 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80000948#64 (fun e => e = c) (WriteRegistersPost [2, 9, 10, 18, 1, 8] [(0x80064668, 4, 2#64)] c ra (-1#64)
      [(2, sp), (9, s1), (10, -1#64), (18, s2), (1, ra), (8, s0)]) := by
  have savedRa := saved 72 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> simp only [OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (openX0948Seg ++ openX09f4Seg) 0x80000948#64
        [(10, 0x80064668#64), (9, 2#64), (2, nativeStack sp 80)] (htifOpenRestoreLoads c.σ.mem sp) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 9, 2]; decide
      shape := by change ChainOK _ [10, 9, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := htifOpenErrnoSet_code leaf.image
        have slotNat (k : Nat) (h : k ≤ 80) :
            (nativeStack sp 80 + BitVec.ofNat 64 k).toNat = nativeFrameBase sp 80 + k := by
          rw [nativeStack, frame.address k h, frame.slot_nat h]
        chain_facts code with "Vsa.Sim.Code._open_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 0x80064668) 4 by constructor <;> decide).sw rfl
            (by simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, Nat.reduceEqDiff, open_se0, BitVec.add_zero])
        · rw [stepMemM_store (by rfl)]
          exact memFacts_writeLog ((frame.read_slot (off := 64) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)))
            (fun _ => by
            simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
              Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, OutLRange, and_true, open_se0, BitVec.add_zero,
              stepMemM_skip, IsStore, Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide]
            rw [slotNat _ (by decide)]
            have := frame.lower; unfold nativeFrameBase heapEnd at *; omega)
        · exact memFacts_writeLog ((frame.read_slot (off := 72) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)))
            (fun _ => by
            simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
              Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, OutLRange, and_true, open_se0, BitVec.add_zero,
              stepMemM_skip, IsStore, Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide]
            rw [slotNat _ (by decide)]
            have := frame.lower; unfold nativeFrameBase heapEnd at *; omega)
        · simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, stepMemM_skip, IsStore]
          exact memFacts_writeLog ((frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)))
            (fun _ => by
            simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
              Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, OutLRange, and_true, open_se0, BitVec.add_zero,
              stepMemM_skip, IsStore, Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide]
            rw [slotNat _ (by decide)]
            have := frame.lower; unfold nativeFrameBase heapEnd at *; omega)
        · simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, stepMemM_skip, IsStore]
          exact memFacts_writeLog ((frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide)))
            (fun _ => by
            simp only [htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
              Option.getD_some, ite_true, ite_false, Nat.reduceEqDiff, OutLRange, and_true, open_se0, BitVec.add_zero,
              stepMemM_skip, IsStore, Nat.reduceAdd, BitVec.toNat_ofNat, Nat.reduceMod, show Functions.sign_extend (m := 64) 64#12 = 64#64 by decide, show Functions.sign_extend (m := 64) 72#12 = 72#64 by decide, show Functions.sign_extend (m := 64) 48#12 = 48#64 by decide, show Functions.sign_extend (m := 64) 56#12 = 56#64 by decide]
            rw [slotNat _ (by decide)]
            have := frame.lower; unfold nativeFrameBase heapEnd at *; omega)
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · simp only [openX0948Seg, openX09f4Seg, evalBlocks, evalBlock, SegEvalState.init, htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, List.cons_append, List.nil_append,
      open_se0, BitVec.add_zero]
    rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 72)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [openX0948Seg, openX09f4Seg, evalBlocks, evalBlock, SegEvalState.init, htifopenerrnoset_line_80000948, htifopenerrnoset_line_8000094c, htifopenerrnoset_line_80000950, htifopenreturn_line_800009f4, htifopenreturn_line_800009f8, htifopenreturn_line_800009fc, htifopenreturn_line_80000a00, htifopenreturn_line_80000a04, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, htifOpenRestoreLoads, List.map_cons,
      List.map_nil, read8_value, List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 80#12 = 80#64 by decide, nativeStack_restore, open_se0, BitVec.add_zero,
      show (0#64 + Functions.sign_extend (m := 64) 4095#12) = -1#64 by decide,
      saved 56 s1 (by simp), saved 48 s2 (by simp), savedRa, saved 64 s0 (by simp)]
  · rfl
  · decide

open Sail in
/-- `auipc a5; lw a5,1376(a5)` at 0x8004d7e8: the global `errno`. -/
theorem open_r_errno_load : 2147801064#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 96151#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1376#12 = BitVec.ofNat 64 0x80064d48 := by decide

/-- A non-store step leaves the memory a later access sees. -/
theorem memFacts_stepMem_skip {m : Std.ExtHashMap Nat (BitVec 8)} {a b : MInstr} {L L' : GRegs} {bs : List (BitVec 8)}
    (kind : IsStore a.kind = false) (h : MemFacts m L' bs b) : MemFacts (stepMemM m a L) L' bs b := by
  rw [stepMemM_skip kind]; exact h

theorem open_r_failed : guardB bop.BEQ (-1#64) (0#64 + Functions.sign_extend (m := 64) 4095#12) = true := by decide

def openRReturnLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp : BitVec 64) (w : List (BitVec 8)) :
    List (List (BitVec 8)) := [w, read8 m (nativeFrameBase sp 16 + 8), read8 m (nativeFrameBase sp 16 + 0)]

/-- `_open` failed and the global `errno` is clear: return -1. -/
theorem open_r_fail_zero (c : Config) (sp ra s0 oldra : BitVec 64) (w : List (BitVec 8)) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 16) (regs : GHolds c.σ [(10, -1#64), (2, nativeStack sp 16)])
    (global : read4 c.σ.mem 0x80064d48 = w) (zero : bytesVal .lw w = 0#64)
    (saved : ∀ off value, (off, value) ∈ [(8, ra), (0, s0)] →
      bytesT c.σ.mem (nativeFrameBase sp 16 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8004d7d0#64 (fun e => e = c)
      (WriteRegistersPost [2, 8, 1, 15] [] c ra (-1#64) [(2, sp), (8, s0), (1, ra), (15, 0#64), (10, -1#64)]) := by
  have savedRa := saved 8 ra (by simp)
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (open_rXd7d0TSeg ++ open_rXd7e8TSeg ++ open_rXd7d8Seg) 0x8004d7d0#64
        [(10, -1#64), (2, nativeStack sp 16)] (openRReturnLoads c.σ.mem sp w) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := openRCheck_code leaf.image
        chain_facts code with "Vsa.Sim.Code._open_r_at_"
        · change guardB bop.BEQ (-1#64) (0#64 + Functions.sign_extend (m := 64) 4095#12) = true
          exact open_r_failed
        · refine memFacts_stepMem_skip rfl <| memFacts_writeLog ((show ReadWindow (BitVec.ofNat 64 0x80064d48) 4 by constructor <;> decide).lw rfl
            (by simp only [openrcheck_line_8004d7d0, openrerrno_line_8004d7e8, openrerrno_line_8004d7ec, openrreturn_line_8004d7d8, openrreturn_line_8004d7dc, openrreturn_line_8004d7e0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
                  ite_false, imm20Of, Nat.reduceEqDiff]
                exact open_r_errno_load) (by rw [← global]; exact read4_pins _ _)) (fun _ => trivial)
        · change guardB bop.BEQ (bytesVal .lw w) 0#64 = true
          rw [zero]; decide
        · exact memFacts_writeLog (memFacts_writeLog ((frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl
            (frame.pins_slot c (by decide))) (fun _ => trivial)) (fun _ => trivial)
        · exact memFacts_stepMem_skip rfl <| memFacts_writeLog (memFacts_writeLog ((frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl
            (frame.pins_slot c (by decide))) (fun _ => trivial)) (fun _ => trivial)
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 16 + 8)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [open_rXd7d0TSeg, open_rXd7e8TSeg, open_rXd7d8Seg, evalBlocks, evalBlock, SegEvalState.init, openrcheck_line_8004d7d0, openrerrno_line_8004d7e8, openrerrno_line_8004d7ec, openrreturn_line_8004d7d8, openrreturn_line_8004d7dc, openrreturn_line_8004d7e0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, openRReturnLoads, read8_value,
      List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, nativeStack_restore, zero, savedRa,
      saved 0 s0 (by simp)]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
