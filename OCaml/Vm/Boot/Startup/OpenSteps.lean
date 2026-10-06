import OCaml.Vm.Boot.Startup.LibOpenEntryNormalized
import OCaml.Vm.Boot.Startup.LibOpenEntryImage
import OCaml.Vm.Boot.Startup.LibOpenEntryCallInterface
import OCaml.Vm.Boot.Startup.ResolveRun
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
end OCaml.Vm.Boot.Startup
