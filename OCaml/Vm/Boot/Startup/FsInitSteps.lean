import OCaml.Vm.Boot.Startup.FsInitSaveNormalized
import OCaml.Vm.Boot.Startup.FsInitSaveImage
import OCaml.Vm.Boot.Startup.FsInitHeaderNormalized
import OCaml.Vm.Boot.Startup.FsInitHeaderImage
import OCaml.Vm.Boot.Startup.FsInitFdsNormalized
import OCaml.Vm.Boot.Startup.FsInitFdsImage
import OCaml.Vm.Boot.Startup.FsInitFirstNormalized
import OCaml.Vm.Boot.Startup.FsInitFirstImage
import OCaml.Vm.Boot.Startup.FsInitLoopSaveNormalized
import OCaml.Vm.Boot.Startup.FsInitLoopSaveImage
import OCaml.Vm.Boot.Startup.FsInitSkipNormalized
import OCaml.Vm.Boot.Startup.FsInitSkipImage
import OCaml.Vm.Boot.Startup.FsInitScanNormalized
import OCaml.Vm.Boot.Startup.FsInitScanImage
import OCaml.Vm.Boot.Startup.FsInitSlashNormalized
import OCaml.Vm.Boot.Startup.FsInitSlashImage
import OCaml.Vm.Boot.Startup.FsInitAfterNormalized
import OCaml.Vm.Boot.Startup.FsInitAfterImage
import OCaml.Vm.Boot.Startup.FsInitMissedNormalized
import OCaml.Vm.Boot.Startup.FsInitMissedImage
import OCaml.Vm.Boot.Startup.FsInitNodeNormalized
import OCaml.Vm.Boot.Startup.FsInitNodeImage
import OCaml.Vm.Boot.Startup.FsInitFileNormalized
import OCaml.Vm.Boot.Startup.FsInitFileImage
import OCaml.Vm.Boot.Startup.FsInitFile2Normalized
import OCaml.Vm.Boot.Startup.FsInitFile2Image
import OCaml.Vm.Boot.Startup.FsInitNextNormalized
import OCaml.Vm.Boot.Startup.FsInitNextImage
import OCaml.Vm.Boot.Startup.FsInitReturnNormalized
import OCaml.Vm.Boot.Startup.FsInitReturnImage
import OCaml.Vm.Boot.Startup.FsInitStrchrNormalized
import OCaml.Vm.Boot.Startup.FsInitStrchrCallInterface
import OCaml.Vm.Boot.Startup.FsInitLengthNormalized
import OCaml.Vm.Boot.Startup.FsInitLengthCallInterface
import OCaml.Vm.Boot.Startup.FsInitChildNormalized
import OCaml.Vm.Boot.Startup.FsInitChildCallInterface
import OCaml.Vm.Boot.Startup.FsInitNewNormalized
import OCaml.Vm.Boot.Startup.FsInitNewCallInterface
import OCaml.Vm.Boot.Startup.BlockCall
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Sim.ClosureLayout
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- An aligned halfword store stays in RAM above the HTIF registers. -/
theorem WriteWindow.sh {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : WriteWindow x 2)
    (kind : a.kind = .sh) (address : eaddrM a L = x) : MemFacts m L bs a := by
  simp only [MemFacts, kind, address]
  refine ⟨h.lower, h.upper, ?_, h.aligned⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

end OCaml.Vm.Primitives

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! htif.c's `fs_init` (the out-of-line `fs_init.part.0`) for the one
embedded file "/prog". -/

def fsInitSlots (ra s0 s3 s6 s7 : BitVec 64) : List (Nat × BitVec 64) :=
  [(56, s3), (32, s6), (24, s7), (88, ra), (80, s0)]
def fsInitLog (sp ra s0 s3 s6 s7 : BitVec 64) : List WEntry :=
  nativeWordLog sp 96 (fsInitSlots ra s0 s3 s6 s7) ++ [(Layout.sym_files, 2, 257#64)]
def fsInitInput (sp ra s0 s3 s6 s7 a0 : BitVec 64) : GRegs :=
  [(2, sp), (19, s3), (22, s6), (23, s7), (1, ra), (8, s0), (10, a0)]

open Sail in
/-- `auipc s3; addi s3,s3,348` at 0x8000036c: the `files` table. -/
theorem files_auipc : 2147484524#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 416151#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 348#12 + Functions.sign_extend (m := 64) 0#12 = BitVec.ofNat 64 Layout.sym_files := by
  decide

local macro "fs_addr" : tactic =>
  `(tactic| (simp only [fsinitsave_line_80000350, fsinitsave_line_80000354, fsinitsave_line_80000358, fsinitsave_line_8000035c, fsinitsave_line_80000360, fsinitsave_line_80000364, fsinitsave_line_80000368, fsinitsave_line_8000036c, fsinitsave_line_80000370, fsinitsave_line_80000374, eaddrM, srcVal, lookupG, runGM, stepGM,
    eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]; decide))

theorem imageOutside_append {l1 l2 : List WEntry} (h1 : ImageOutside l1) (h2 : ImageOutside l2) :
    ImageOutside (l1 ++ l2) :=
  ⟨OCaml.Vm.Sim.outLRange_append h1.text h2.text, OCaml.Vm.Sim.outLRange_append h1.rodata h2.rodata⟩

theorem fsInitLog_image {sp ra s0 s3 s6 s7} (frame : NativeFrame sp 96) :
    ImageOutside (fsInitLog sp ra s0 s3 s6 s7) := by
  apply imageOutside_append (frame.image_outside (frame.word_log_inside (fun off value member => by
    simp only [fsInitSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    omega)))
  constructor <;> simp only [OutLRange] <;> decide

def fsInitSaved (sp ra s0 s6 s7 a0 : BitVec 64) : GRegs :=
  [(19, BitVec.ofNat 64 Layout.sym_files), (15, 257#64), (2, nativeStack sp 96), (22, s6), (23, s7), (1, ra), (8, s0),
    (10, a0)]

theorem fs_init_save (c : Config) (sp ra s0 s3 s6 s7 a0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (fsInitInput sp ra s0 s3 s6 s7 a0)) :
    FnSummary 0x80000350#64 (fun e => e = c)
      (WriteRegistersPost [2, 15, 19] (fsInitLog sp ra s0 s3 s6 s7) c 0x80000378#64 a0
        (fsInitSaved sp ra s0 s6 s7 a0)) := by
  apply registers_of_blocks leaf.image (fsInitLog_image frame)
    (block_summary _ _ _ _ _ (show BlockInput fs_init_part_0X0350Seg 0x80000350#64 (fsInitInput sp ra s0 s3 s6 s7 a0) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 19, 22, 23, 1, 8, 10]; decide
      shape := by change ChainOK _ [2, 19, 22, 23, 1, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 96) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 96 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 88 (by decide) (by decide)).sd rfl rfl
        · exact (slot 80 (by decide) (by decide)).sd rfl rfl
        · exact (show WriteWindow (BitVec.ofNat 64 Layout.sym_files) 2 by constructor <;> decide).sh rfl
            (by simp only [fsinitsave_line_8000036c, fsinitsave_line_80000370, fsinitsave_line_80000374, eaddrM,
                  srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of,
                  Nat.reduceEqDiff]
                exact files_auipc) }))
  · simp only [fs_init_part_0X0350Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitsave_line_80000350, fsinitsave_line_80000354, fsinitsave_line_80000358, fsinitsave_line_8000035c, fsinitsave_line_80000360, fsinitsave_line_80000364, fsinitsave_line_80000368, fsinitsave_line_8000036c, fsinitsave_line_80000370, fsinitsave_line_80000374, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitInput, imm20Of, fsInitLog, fsInitSlots, nativeWordLog, List.map,
      List.nil_append, List.cons_append]
    rw [files_auipc, show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide,
      show Functions.sign_extend (m := 64) 257#12 = 257#64 by decide, BitVec.zero_add]
    rfl
  · rfl
  · simp only [fs_init_part_0X0350Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitsave_line_80000350, fsinitsave_line_80000354, fsinitsave_line_80000358, fsinitsave_line_8000035c, fsinitsave_line_80000360, fsinitsave_line_80000364, fsinitsave_line_80000368, fsinitsave_line_8000036c, fsinitsave_line_80000370, fsinitsave_line_80000374, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitInput, imm20Of, fsInitSaved]
    rw [show Functions.sign_extend (m := 64) 4000#12 = -BitVec.ofNat 64 96 by decide,
      show Functions.sign_extend (m := 64) 257#12 = 257#64 by decide, BitVec.zero_add]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by rw [← files_auipc]; rfl, rfl⟩
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
