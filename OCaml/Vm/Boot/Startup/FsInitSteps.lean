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
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.GRegsFrame
import OCaml.Vm.Primitives.BlockPins
import OCaml.Vm.Boot.Startup.NewNodeSteps
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
open Sail in
theorem embed_auipc : 2147484536#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 109054743#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 3208#12 = BitVec.ofNat 64 Layout.sym_embed_start := by
  decide

def fsInitHeadered (sp ra s0 s7 a0 table : BitVec 64) : GRegs :=
  [(15, 2#64), (22, table), (19, BitVec.ofNat 64 Layout.sym_files), (2, nativeStack sp 96), (23, s7), (1, ra), (8, s0),
    (10, a0)]

/-- Load the embedded-file table pointer. -/
theorem fs_init_header (c : Config) (sp ra s0 s6 s7 a0 table : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (fsInitSaved sp ra s0 s6 s7 a0))
    (header : bytesT c.σ.mem Layout.sym_embed_start 8 = table) :
    FnSummary 0x80000378#64 (fun e => e = c)
      (WriteRegistersPost [22, 15] [] c 0x80000384#64 a0 (fsInitHeadered sp ra s0 s7 a0 table)) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput fs_init_part_0X0378Seg 0x80000378#64 (fsInitSaved sp ra s0 s6 s7 a0)
        [read8 c.σ.mem Layout.sym_embed_start] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [19, 15, 2, 22, 23, 1, 8, 10]; decide
      shape := by change ChainOK _ [19, 15, 2, 22, 23, 1, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitHeader_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        exact (show ReadWindow (BitVec.ofNat 64 Layout.sym_embed_start) 8 by constructor <;> decide).ld rfl
          (by simp only [fsinitheader_line_80000378, fsinitheader_line_8000037c, fsinitheader_line_80000380, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
                Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
              exact embed_auipc) (read8_pins _ _) }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X0378Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitheader_line_80000378, fsinitheader_line_8000037c, fsinitheader_line_80000380, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitSaved, imm20Of, read8_value, header, fsInitHeadered]
    rw [show Functions.sign_extend (m := 64) 2#12 = 2#64 by decide, BitVec.zero_add]
  · rfl
  · decide
open Sail in
theorem fds_auipc0 : 2147484552#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 415511#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2600#12 = BitVec.ofNat 64 (Layout.sym_fds + 24) := by decide
open Sail in
theorem fds_auipc1 : 2147484564#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 415511#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2612#12 = BitVec.ofNat 64 (Layout.sym_fds + 48) := by decide
open Sail in
theorem fds_auipc2 : 2147484572#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 415639#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 2556#12 = BitVec.ofNat 64 Layout.sym_fds := by decide

def fdsLog : List WEntry :=
  [(Layout.sym_fds + 24, 4, 2#64), (Layout.sym_fds + 48, 4, 3#64), (Layout.sym_fds, 4, 1#64)]

def fsInitFds (sp ra s0 a0 table : BitVec 64) : GRegs :=
  [(15, 0x8006539c#64), (14, 0x80065394#64), (23, 1#64), (22, table), (19, BitVec.ofNat 64 Layout.sym_files),
    (2, nativeStack sp 96), (1, ra), (8, s0), (10, a0)]

/-- The three standard descriptors. -/
theorem fs_init_fds (c : Config) (sp ra s0 s7 a0 table : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (fsInitHeadered sp ra s0 s7 a0 table)) :
    FnSummary 0x80000384#64 (fun e => e = c)
      (WriteRegistersPost [23, 14, 15] fdsLog c 0x800003a4#64 a0 (fsInitFds sp ra s0 a0 table)) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [fdsLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput fs_init_part_0X0384Seg 0x80000384#64 (fsInitHeadered sp ra s0 s7 a0 table)
        [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 22, 19, 2, 23, 1, 8, 10]; decide
      shape := by change ChainOK _ [15, 22, 19, 2, 23, 1, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitFds_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 24)) 4 by constructor <;> decide).sw rfl
            (by simp only [fsinitfds_line_80000384, fsinitfds_line_80000388, fsinitfds_line_8000038c, fsinitfds_line_80000390, fsinitfds_line_80000394, fsinitfds_line_80000398, fsinitfds_line_8000039c, fsinitfds_line_800003a0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact fds_auipc0)
        · exact (show WriteWindow (BitVec.ofNat 64 (Layout.sym_fds + 48)) 4 by constructor <;> decide).sw rfl
            (by simp only [fsinitfds_line_80000384, fsinitfds_line_80000388, fsinitfds_line_8000038c, fsinitfds_line_80000390, fsinitfds_line_80000394, fsinitfds_line_80000398, fsinitfds_line_8000039c, fsinitfds_line_800003a0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact fds_auipc1)
        · exact (show WriteWindow (BitVec.ofNat 64 Layout.sym_fds) 4 by constructor <;> decide).sw rfl
            (by simp only [fsinitfds_line_80000384, fsinitfds_line_80000388, fsinitfds_line_8000038c, fsinitfds_line_80000390, fsinitfds_line_80000394, fsinitfds_line_80000398, fsinitfds_line_8000039c, fsinitfds_line_800003a0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact fds_auipc2) }))
  · simp only [fs_init_part_0X0384Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitfds_line_80000384, fsinitfds_line_80000388, fsinitfds_line_8000038c, fsinitfds_line_80000390, fsinitfds_line_80000394, fsinitfds_line_80000398, fsinitfds_line_8000039c, fsinitfds_line_800003a0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitHeadered, imm20Of, fdsLog,
      List.nil_append, List.cons_append]
    rw [fds_auipc0, fds_auipc1, fds_auipc2]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    decide
  · rfl
  · simp only [fs_init_part_0X0384Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitfds_line_80000384, fsinitfds_line_80000388, fsinitfds_line_8000038c, fsinitfds_line_80000390, fsinitfds_line_80000394, fsinitfds_line_80000398, fsinitfds_line_8000039c, fsinitfds_line_800003a0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitHeadered, imm20Of, fsInitFds]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    exact ⟨by decide, by decide, by decide⟩
  · rfl
  · decide
def fsReadyLog : List WEntry := [(Layout.sym_fs_ready, 4, 1#64)]

open Sail in
theorem ready_auipc : 2147484584#64 + Functions.sign_extend (m := 64) (BitVec.extractLsb' 12 20 411543#32 +++ 0#12) +
    Functions.sign_extend (m := 64) 1392#12 = BitVec.ofNat 64 Layout.sym_fs_ready := by decide

def fsInitFirst (sp ra a0 table path : BitVec 64) : GRegs :=
  [(15, 0x800643a8#64), (8, path), (14, 0x80065394#64), (23, 1#64), (22, table), (19, BitVec.ofNat 64 Layout.sym_files),
    (2, nativeStack sp 96), (1, ra), (10, a0)]

/-- The first entry's path; mark the file system ready. -/
theorem fs_init_first (c : Config) (sp ra s0 a0 table path : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (fsInitFds sp ra s0 a0 table)) (window : ReadWindow table 8)
    (entry : bytesT c.σ.mem table.toNat 8 = path) (nonnull : path ≠ 0#64) :
    FnSummary 0x800003a4#64 (fun e => e = c)
      (WriteRegistersPost [8, 15] fsReadyLog c 0x800003b4#64 a0 (fsInitFirst sp ra a0 table path)) := by
  apply registers_of_blocks leaf.image (by constructor <;> simp only [fsReadyLog, OutLRange] <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput fs_init_part_0X03a4FSeg 0x800003a4#64 (fsInitFds sp ra s0 a0 table)
        [read8 c.σ.mem table.toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 14, 23, 22, 19, 2, 1, 8, 10]; decide
      shape := by change ChainOK _ [15, 14, 23, 22, 19, 2, 1, 8, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitFirst_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact window.ld rfl (by change table + Functions.sign_extend (m := 64) 0#12 = table
                                  rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero])
            (read8_pins _ _)
        · exact (show WriteWindow (BitVec.ofNat 64 Layout.sym_fs_ready) 4 by constructor <;> decide).sw rfl
            (by simp only [fsinitfirst_line_800003a4, fsinitfirst_line_800003a8, fsinitfirst_line_800003ac, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some,
                  ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
                exact ready_auipc)
        · change guardB bop.BEQ (bytesVal .ld (read8 c.σ.mem table.toNat)) 0#64 = false
          rw [read8_value, entry]
          exact beq_eq_false_iff_ne.mpr nonnull }))
  · simp only [fs_init_part_0X03a4FSeg, evalBlocks, evalBlock, SegEvalState.init, fsinitfirst_line_800003a4, fsinitfirst_line_800003a8, fsinitfirst_line_800003ac, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitFds, imm20Of, fsReadyLog,
      List.nil_append, List.cons_append]
    rw [ready_auipc]
    decide
  · rfl
  · simp only [fs_init_part_0X03a4FSeg, evalBlocks, evalBlock, SegEvalState.init, fsinitfirst_line_800003a4, fsinitfirst_line_800003a8, fsinitfirst_line_800003ac, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsInitFds, imm20Of, read8_value, entry, fsInitFirst]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    decide
  · rfl
  · decide
def fsLoopSlots (s1 s2 s4 s5 s8 s9 : BitVec 64) : List (Nat × BitVec 64) :=
  [(64, s2), (48, s4), (40, s5), (72, s1), (16, s8), (8, s9)]
def fsLoopLog (sp s1 s2 s4 s5 s8 s9 : BitVec 64) : List WEntry := nativeWordLog sp 96 (fsLoopSlots s1 s2 s4 s5 s8 s9)

theorem fsLoopLog_inside {sp s1 s2 s4 s5 s8 s9} (frame : NativeFrame sp 96) :
    LogInW [⟨nativeFrameBase sp 96, sp.toNat⟩] (fsLoopLog sp s1 s2 s4 s5 s8 s9) := by
  apply frame.word_log_inside
  intro off value member
  simp only [fsLoopSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

def fsLoopInput (sp ra a0 table path s1 s2 s4 s5 s8 s9 : BitVec 64) : GRegs :=
  fsInitFirst sp ra a0 table path ++ [(9, s1), (18, s2), (20, s4), (21, s5), (24, s8), (25, s9)]

def fsLoopSaved (sp ra a0 table path s1 s8 s9 : BitVec 64) : GRegs :=
  [(18, 47#64), (21, 0#64), (20, table), (15, 0x800643a8#64), (8, path), (14, 0x80065394#64), (23, 1#64), (22, table),
    (19, BitVec.ofNat 64 Layout.sym_files), (2, nativeStack sp 96), (1, ra), (10, a0), (9, s1), (24, s8), (25, s9)]

/-- Save s1, s2, s4, s5, s8 and s9; start at the first table entry. -/
theorem fs_init_loop_save (c : Config) (sp ra a0 table path s1 s2 s4 s5 s8 s9 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 96) (regs : GHolds c.σ (fsLoopInput sp ra a0 table path s1 s2 s4 s5 s8 s9)) :
    FnSummary 0x800003b4#64 (fun e => e = c)
      (WriteRegistersPost [20, 21, 18] (fsLoopLog sp s1 s2 s4 s5 s8 s9) c 0x800003d8#64 a0
        (fsLoopSaved sp ra a0 table path s1 s8 s9)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (fsLoopLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput fs_init_part_0X03b4Seg 0x800003b4#64
        (fsLoopInput sp ra a0 table path s1 s2 s4 s5 s8 s9) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [15, 8, 14, 23, 22, 19, 2, 1, 10, 9, 18, 20, 21, 24, 25]; decide
      shape := by change ChainOK _ [15, 8, 14, 23, 22, 19, 2, 1, 10, 9, 18, 20, 21, 24, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitLoopSave_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 96) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 96 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · exact (slot 16 (by decide) (by decide)).sd rfl rfl
        · exact (slot 8 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X03b4Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitloopsave_line_800003b4, fsinitloopsave_line_800003b8, fsinitloopsave_line_800003bc, fsinitloopsave_line_800003c0, fsinitloopsave_line_800003c4, fsinitloopsave_line_800003c8, fsinitloopsave_line_800003cc, fsinitloopsave_line_800003d0, fsinitloopsave_line_800003d4, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsLoopInput, fsInitFirst, imm20Of,
      fsLoopSaved, List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add,
      show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide, BitVec.add_zero]
  · rfl
  · decide
/-- The loop's registers the skip block reads (`ra` is saved, `a0` is dead). -/
def fsSkipInput (sp table path s1 s8 s9 : BitVec 64) : GRegs :=
  [(18, 47#64), (21, 0#64), (20, table), (15, 0x800643a8#64), (8, path), (14, 0x80065394#64), (23, 1#64), (22, table),
    (19, BitVec.ofNat 64 Layout.sym_files), (2, nativeStack sp 96), (9, s1), (24, s8), (25, s9)]

theorem fsSkipInput_of_saved {σ : MState} {sp ra a0 table path s1 s8 s9 : BitVec 64}
    (regs : GHolds σ (fsLoopSaved sp ra a0 table path s1 s8 s9)) : GHolds σ (fsSkipInput sp table path s1 s8 s9) :=
  gholds_select regs _ fun n v member => by
    simp only [fsSkipInput, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The registers after the leading '/' is skipped: the cursor at `path + 1`, its byte loaded. -/
def fsSkipped (sp table path s9 : BitVec 64) (b : BitVec 8) : List (Nat × BitVec 64) :=
  [(10, path + 1#64), (11, 47#64), (15, nameByteWord b), (8, path + 1#64), (24, path + 1#64), (9, 0#64),
    (18, 47#64), (21, 0#64), (20, table), (14, 2147898260#64), (23, 1#64), (22, table),
    (19, BitVec.ofNat 64 Layout.sym_files), (2, nativeStack sp 96), (25, s9)]

/-- Skip the path's leading '/' and reach its first name byte. -/
theorem fs_init_skip (c : Config) (sp ra table path s1 s8 s9 : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (fsSkipInput sp table path s1 s8 s9)) (window : ReadWindow path 2)
    (slash : (c.σ.mem[path.toNat]?).getD 0 = 47#8) (first : (c.σ.mem[(path + 1#64).toNat]?).getD 0 = b)
    (notSlash : b ≠ 47#8) :
    FnSummary 0x800003d8#64 (fun e => e = c)
      (WriteRegistersPost [15, 9, 11, 10, 24, 8] [] c 0x800003ec#64 (path + 1#64) (fsSkipped sp table path s9 b)) := by
  have w0 : ReadWindow path 1 := ⟨window.lower, by have := window.upper; omega,
    by rcases window.htif with h | h; exact Or.inl (by omega); exact Or.inr h⟩
  have w1 : ReadWindow (path + 1#64) 1 := by
    have nat : (path + 1#64).toNat = path.toNat + 1 := by
      rw [BitVec.toNat_add]; have := window.upper; rw [show (1#64).toNat = 1 from rfl]; omega
    exact ⟨by rw [nat]; exact Nat.le_trans window.lower (by omega), by rw [nat]; have := window.upper; omega,
      by rw [nat]; rcases window.htif with h | h; exact Or.inl (by omega); exact Or.inr (by omega)⟩
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X03d8TSeg ++ fs_init_part_0X0444Seg ++
        fs_init_part_0X0434TSeg) 0x800003d8#64 (fsSkipInput sp table path s1 s8 s9) [[47#8], [b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [18, 21, 20, 15, 8, 14, 23, 22, 19, 2, 9, 24, 25]; decide
      shape := by change ChainOK _ [18, 21, 20, 15, 8, 14, 23, 22, 19, 2, 9, 24, 25] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitSkip_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact w0.lbu rfl (by change path + Functions.sign_extend (m := 64) 0#12 = path
                               rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero]) slash
        · change guardB bop.BEQ (bytesVal .lbu [47#8]) 47#64 = true
          decide
        · exact w1.lbu rfl (by simp only [fsinitskip_line_800003d8, fsinitskip_line_800003dc, fsinitskip_line_800003e0, fsinitskip_line_800003e4, fsinitslash_line_80000444, fsinitslash_line_80000448, fsinitscan_line_80000434, fsinitscan_line_80000438, fsinitscan_line_8000043c, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM,
                                   Option.getD_some, ite_true, ite_false, fsSkipInput, Nat.reduceAdd, Nat.reduceEqDiff]
                               rw [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero,
                                 BitVec.add_zero,
                                 show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide]) first
        · change guardB bop.BNE (bytesVal .lbu [b]) 47#64 = true
          rw [name_lbu_value]
          exact bne_iff_ne.mpr (nameByteWord_ne_of notSlash (by decide)) }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X03d8TSeg, fs_init_part_0X0444Seg, fs_init_part_0X0434TSeg, evalBlocks, evalBlock,
      SegEvalState.init, fsinitskip_line_800003d8, fsinitskip_line_800003dc, fsinitskip_line_800003e0, fsinitskip_line_800003e4, fsinitslash_line_80000444, fsinitslash_line_80000448, fsinitscan_line_80000434, fsinitscan_line_80000438, fsinitscan_line_8000043c, runGM, ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM,
      wentryM, widthOfM, List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false,
      fsSkipInput, List.cons_append, List.nil_append, name_lbu_value]
    simp only [show Functions.sign_extend (m := 64) 1#12 = 1#64 by decide,
      show Functions.sign_extend (m := 64) 47#12 = 47#64 by decide,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add]
    rfl
  · rfl
  · decide

/-- Skip the leading '/' and call `strchr(path + 1, '/')`. -/
theorem fs_init_strchr_call (c : Config) (sp ra table path s1 s8 s9 : BitVec 64) (b : BitVec 8)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (fsSkipInput sp table path s1 s8 s9)) (window : ReadWindow path 2)
    (slash : (c.σ.mem[path.toNat]?).getD 0 = 47#8) (first : (c.σ.mem[(path + 1#64).toNat]?).getD 0 = b)
    (notSlash : b ≠ 47#8) :
    FnSummary 0x800003d8#64 (fun e => e = c)
      (WriteRegistersPost ([15, 9, 11, 10, 24, 8] ++ [1]) [] c jal_800003ec_call.target (path + 1#64)
        ((1, jal_800003ec_call.link) :: fsSkipped sp table path s9 b)) :=
  block_then_call c jal_800003ec_call_shape jal_800003ec_call_decode (fun _ h => jal_800003ec_call_pins h)
    (fs_init_skip c sp ra table path s1 s8 s9 b leaf regs window slash first notSlash)
    (by simp only [fsSkipped, keysG]; decide) (by simp only [fsSkipped, KeysAvoidRa, keysG]; decide) rfl

theorem fs_init_strlen_front (c : Config) (ra s0 s1 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 0#64), (8, s0), (9, s1)]) :
    FnSummary 0x800003f0#64 (fun e => e = c) (WriteRegistersPost [24, 11, 10] [] c jal_80000454_call.pc s0 [(10, s0), (11, s0), (24, 0#64), (8, s0), (9, s1)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X03f0TSeg ++ fs_init_part_0X0450Seg) 0x800003f0#64 [(10, 0#64), (8, s0), (9, s1)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 8, 9]; decide
      shape := by change ChainOK _ [10, 8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitAfter_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · change guardB bop.BEQ 0#64 0#64 = true
          decide }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X03f0TSeg, fs_init_part_0X0450Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitafter_line_800003f0, fsinitafter_line_800003f4, fsinitafter_line_800003f8, fsinitlength_line_80000450, runGM, ldsRunM, wlogM, stepGM,
      stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append, List.nil_append]
    simp only [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add]
  · rfl
  · decide

theorem fs_init_child_front (c : Config) (ra len s0 s1 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, len), (8, s0), (9, s1)]) (nonzero : len ≠ 0#64) :
    FnSummary 0x80000458#64 (fun e => e = c) (WriteRegistersPost [24, 12, 11, 10] [] c jal_8000046c_call.pc s1 [(10, s1), (11, s0), (12, len), (24, len), (8, s0), (9, s1)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X0458FSeg ++ fs_init_part_0X0460Seg) 0x80000458#64 [(10, len), (8, s0), (9, s1)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 8, 9]; decide
      shape := by change ChainOK _ [10, 8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitChild_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · change guardB bop.BEQ len 0#64 = false
          exact beq_eq_false_iff_ne.mpr nonzero }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X0458FSeg, fs_init_part_0X0460Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitchild_line_80000458, fsinitchild_line_80000460, fsinitchild_line_80000464, fsinitchild_line_80000468, runGM, ldsRunM, wlogM, stepGM,
      stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append, List.nil_append]
    simp only [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add]
  · rfl
  · decide

theorem fs_init_new_front (c : Config) (ra s0 s1 s8 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, -1#64), (24, s8), (8, s0), (9, s1)]) :
    FnSummary 0x80000470#64 (fun e => e = c) (WriteRegistersPost [12, 11, 10, 13] [] c jal_80000544_call.pc s1 [(13, 0#64), (10, s1), (11, s0), (12, s8), (24, s8), (8, s0), (9, s1)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X0470TSeg ++ fs_init_part_0X0534Seg) 0x80000470#64 [(10, -1#64), (24, s8), (8, s0), (9, s1)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 24, 8, 9]; decide
      shape := by change ChainOK _ [10, 24, 8, 9] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitMissed_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · change guardB bop.BLT (-1#64) 0#64 = true
          decide }))
  · rfl
  · rfl
  · simp only [fs_init_part_0X0470TSeg, fs_init_part_0X0534Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitnew_line_80000534, fsinitnew_line_80000538, fsinitnew_line_8000053c, fsinitnew_line_80000540, runGM, ldsRunM, wlogM, stepGM,
      stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append, List.nil_append]
    simp only [show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero, BitVec.zero_add]
  · rfl
  · decide

theorem fs_init_strlen_call (c : Config) (ra s0 s1 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 0#64), (8, s0), (9, s1)]) :
    FnSummary 0x800003f0#64 (fun e => e = c)
      (WriteRegistersPost ([24, 11, 10] ++ [1]) [] c jal_80000454_call.target s0
        ((1, jal_80000454_call.link) :: [(10, s0), (11, s0), (24, 0#64), (8, s0), (9, s1)])) :=
  block_then_call c jal_80000454_call_shape jal_80000454_call_decode (fun _ h => jal_80000454_call_pins h)
    (fs_init_strlen_front c ra s0 s1 leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

theorem fs_init_child_call (c : Config) (ra len s0 s1 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, len), (8, s0), (9, s1)]) (nonzero : len ≠ 0#64) :
    FnSummary 0x80000458#64 (fun e => e = c)
      (WriteRegistersPost ([24, 12, 11, 10] ++ [1]) [] c jal_8000046c_call.target s1
        ((1, jal_8000046c_call.link) :: [(10, s1), (11, s0), (12, len), (24, len), (8, s0), (9, s1)])) :=
  block_then_call c jal_8000046c_call_shape jal_8000046c_call_decode (fun _ h => jal_8000046c_call_pins h)
    (fs_init_child_front c ra len s0 s1 leaf regs nonzero) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

theorem fs_init_new_call (c : Config) (ra s0 s1 s8 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, -1#64), (24, s8), (8, s0), (9, s1)]) :
    FnSummary 0x80000470#64 (fun e => e = c)
      (WriteRegistersPost ([12, 11, 10, 13] ++ [1]) [] c jal_80000544_call.target s1
        ((1, jal_80000544_call.link) :: [(13, 0#64), (10, s1), (11, s0), (12, s8), (24, s8), (8, s0), (9, s1)])) :=
  block_then_call c jal_80000544_call_shape jal_80000544_call_decode (fun _ h => jal_80000544_call_pins h)
    (fs_init_new_front c ra s0 s1 s8 leaf regs) (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa, keysG]; decide) rfl

/-- The slot-1 fields `fs_init` sets for an embedded file: data, read-only, size and capacity. -/
def fsFileLog (start stop : BitVec 64) : List WEntry :=
  [(slotOne + 24, 8, start), (slotOne + 52, 1, 1#64), (slotOne + 40, 8, stop - start), (slotOne + 32, 8, stop - start)]

def fsFileLoads (m : Std.ExtHashMap Nat (BitVec 8)) (table : BitVec 64) : List (List (BitVec 8)) :=
  [[0#8], read8 m (table + 8#64).toNat, read8 m (table + 16#64).toNat]

def fsFiled (table start stop : BitVec 64) : GRegs :=
  [(14, stop - start), (13, start), (15, childFirst), (10, 1#64), (19, BitVec.ofNat 64 Layout.sym_files), (20, table),
    (23, 1#64)]

local macro "file_addr" : tactic =>
  `(tactic| (simp only [fsinitfile_line_80000474, fsinitfile_line_80000478, fsinitfile_line_8000047c, fsinitfile_line_80000480, fsinitfile_line_80000484, fsinitfile_line_8000048c, fsinitfile_line_80000490, fsinitfile2_line_80000494, fsinitfile2_line_80000498, fsinitfile2_line_8000049c, fsinitfile2_line_800004a0, fsinitfile2_line_800004a4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
    ite_false, imm20Of, Nat.reduceEqDiff, childFirst]; decide))

/-- `((1 << 3) - 1) << 3`: slot 1's offset in `files`. -/
theorem file_slot_index : Sail.shift_bits_left (Sail.shift_bits_left (1#64) (Sail.BitVec.extractLsb ((3#12).extractLsb' 0 6) 5 0) - 1#64)
    (Sail.BitVec.extractLsb ((3#12).extractLsb' 0 6) 5 0) = 56#64 := by decide

theorem file_slot24 : (BitVec.ofNat 64 Layout.sym_files + 56#64 + 24#64).toNat = slotOne + 24 := by decide

local macro "entry_addr" : tactic =>
  `(tactic| (simp only [fsinitfile_line_80000474, fsinitfile_line_80000478, fsinitfile_line_8000047c, fsinitfile_line_80000480, fsinitfile_line_80000484, fsinitfile_line_8000048c, fsinitfile_line_80000490, fsinitfile2_line_80000494, fsinitfile2_line_80000498, fsinitfile2_line_8000049c, fsinitfile2_line_800004a0, fsinitfile2_line_800004a4, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
    ite_false, imm20Of, Nat.reduceEqDiff, show Functions.sign_extend (m := 64) 8#12 = 8#64 by decide,
    show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide]))

/-- `new_node` gave slot 1, a file: copy the embedded entry's extent into it. -/
theorem fs_init_file (c : Config) (ra table : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(10, 1#64), (19, BitVec.ofNat 64 Layout.sym_files), (20, table), (23, 1#64)])
    (dirZero : (c.σ.mem[slotOne + 1]?).getD 0 = 0#8) (startW : ReadWindow (table + 8#64) 8)
    (stopW : ReadWindow (table + 16#64) 8)
    (apart : (table + 16#64).toNat + 8 ≤ slotOne + 24 ∨ slotOne + 32 ≤ (table + 16#64).toNat) :
    FnSummary 0x80000548#64 (fun e => e = c)
      (WriteRegistersPost [15, 14, 13] (fsFileLog (bytesT c.σ.mem (table + 8#64).toNat 8)
        (bytesT c.σ.mem (table + 16#64).toNat 8)) c 0x800004a8#64 1#64
        (fsFiled table (bytesT c.σ.mem (table + 8#64).toNat 8) (bytesT c.σ.mem (table + 16#64).toNat 8))) := by
  have dirW : ReadWindow (childFirst + 1#64) 1 := (slotOne_write 1 1 (by decide) (by decide)).read
  apply registers_of_blocks leaf.image (by
      constructor <;> simp only [fsFileLog, OutLRange] <;> refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;>
        unfold slotOne Layout.sym_files <;> decide)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X0548TSeg ++ fs_init_part_0X0474FSeg ++
        fs_init_part_0X048cSeg ++ fs_init_part_0X0494Seg) 0x80000548#64
        [(10, 1#64), (19, BitVec.ofNat 64 Layout.sym_files), (20, table), (23, 1#64)] (fsFileLoads c.σ.mem table) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 19, 20, 23]; decide
      shape := by change ChainOK _ [10, 19, 20, 23] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitNode_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · change guardB bop.BGE 1#64 0#64 = true
          decide
        · exact dirW.lbu rfl (by file_addr) (by rw [show (childFirst + 1#64).toNat = slotOne + 1 by decide]; exact dirZero)
        · change guardB bop.BNE (bytesVal .lbu [0#8]) 0#64 = false
          decide
        · exact startW.ld rfl (by entry_addr) (read8_pins _ _)
        · exact (slotOne_write 24 8 (by decide) (by decide)).sd rfl (by file_addr)
        · refine memFacts_writeLog (memFacts_writeLog (memFacts_writeLog
            (stopW.ld rfl (by entry_addr) (read8_pins _ _)) (fun _ => trivial)) (fun _ => trivial))
            (fun _ => ?_)
          simp only [fsinitfile_line_80000474, fsinitfile_line_80000478, fsinitfile_line_8000047c, fsinitfile_line_80000480, fsinitfile_line_80000484, fsinitfile_line_8000048c, fsinitfile_line_80000490, fsinitfile2_line_80000494, fsinitfile2_line_80000498, fsinitfile2_line_8000049c, fsinitfile2_line_800004a0, fsinitfile2_line_800004a4, wlogM, wentryM, widthOfM, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG,
            wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff, OutLRange,
            show Functions.sign_extend (m := 64) 16#12 = 16#64 by decide, shamtOf,
            show Functions.sign_extend (m := 64) 24#12 = 24#64 by decide, and_true]
          rw [file_slot_index, file_slot24]
          exact apart
        · exact (slotOne_write 52 1 (by decide) (by decide)).sb rfl (by file_addr)
        · exact (slotOne_write 40 8 (by decide) (by decide)).sd rfl (by file_addr)
        · exact (slotOne_write 32 8 (by decide) (by decide)).sd rfl (by file_addr) }))
  · simp only [fs_init_part_0X0548TSeg, fs_init_part_0X0474FSeg, fs_init_part_0X048cSeg, fs_init_part_0X0494Seg,
      evalBlocks, evalBlock, SegEvalState.init, fsinitfile_line_80000474, fsinitfile_line_80000478, fsinitfile_line_8000047c, fsinitfile_line_80000480, fsinitfile_line_80000484, fsinitfile_line_8000048c, fsinitfile_line_80000490, fsinitfile2_line_80000494, fsinitfile2_line_80000498, fsinitfile2_line_8000049c, fsinitfile2_line_800004a0, fsinitfile2_line_800004a4, runGM, ldsRunM, wlogM, stepGM,
      stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append, List.nil_append,
      fsFileLoads, read8_value, fsFileLog]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    decide
  · rfl
  · simp only [fs_init_part_0X0548TSeg, fs_init_part_0X0474FSeg, fs_init_part_0X048cSeg, fs_init_part_0X0494Seg,
      evalBlocks, evalBlock, SegEvalState.init, fsinitfile_line_80000474, fsinitfile_line_80000478, fsinitfile_line_8000047c, fsinitfile_line_80000480, fsinitfile_line_80000484, fsinitfile_line_8000048c, fsinitfile_line_80000490, fsinitfile2_line_80000494, fsinitfile2_line_80000498, fsinitfile2_line_8000049c, fsinitfile2_line_800004a0, fsinitfile2_line_800004a4, runGM, ldsRunM, wlogM, stepGM,
      stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons, List.tail_cons,
      Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, imm20Of, List.cons_append, List.nil_append,
      fsFileLoads, read8_value, fsFiled]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true, true_and]
    decide
  · rfl
  · decide

/-- `((1 << 1) + 1) << 3` for the second entry (`s5 = 1`): its offset in the embedded table. -/
theorem next_entry_offset :
    Sail.shift_bits_left
        (Sail.shift_bits_left
            (Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (0#64 + Functions.sign_extend (m := 64) 1#12) 31 0))
            (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 1#12) 5 0) +
          Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (0#64 + Functions.sign_extend (m := 64) 1#12) 31 0))
        (Sail.BitVec.extractLsb (BitVec.extractLsb' 0 6 3#12) 5 0) = 24#64 := by decide

local macro "restore_addr" : tactic =>
  `(tactic| (simp only [fsinitnext_line_800004a8, fsinitnext_line_800004ac, fsinitnext_line_800004b0, fsinitnext_line_800004b4, fsinitnext_line_800004b8, fsinitnext_line_800004bc, fsinitreturn_line_800004c4, fsinitreturn_line_800004c8, fsinitreturn_line_800004cc, fsinitreturn_line_800004d0, fsinitreturn_line_800004d4, fsinitreturn_line_800004d8, fsinitreturn_line_800004dc, fsinitreturn_line_800004e0, fsinitreturn_line_800004e4, fsinitreturn_line_800004e8, fsinitreturn_line_800004ec, fsinitreturn_line_800004f0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
    ite_false, Nat.reduceEqDiff] <;> first | rfl | (congr 1)))

/-- The callee-saved registers `fs_init` restores, at their frame offsets. -/
def fsInitRestored (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : BitVec 64) : List (Nat × BitVec 64) :=
  [(72, s1), (64, s2), (48, s4), (40, s5), (16, s8), (8, s9), (88, ra), (80, s0), (56, s3), (32, s6), (24, s7)]

def fsReturnLoads (m : Std.ExtHashMap Nat (BitVec 8)) (sp table : BitVec 64) : List (List (BitVec 8)) :=
  read8 m (table + 24#64).toNat :: [72, 64, 48, 40, 16, 8, 88, 80, 56, 32, 24].map
    fun off => read8 m (nativeFrameBase sp 96 + off)

/-- The embedded table ends after one entry: restore and return. -/
theorem fs_init_return (c : Config) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 table oldra : BitVec 64)
    (leaf : LeafInput oldra c) (frame : NativeFrame sp 96)
    (regs : GHolds c.σ [(21, 0#64), (22, table), (2, nativeStack sp 96), (10, 1#64)])
    (endW : ReadWindow (table + 24#64) 8) (ended : bytesT c.σ.mem (table + 24#64).toNat 8 = 0#64)
    (saved : ∀ off value, (off, value) ∈ fsInitRestored ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 →
      bytesT c.σ.mem (nativeFrameBase sp 96 + off) 8 = value) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800004a8#64 (fun e => e = c) (WriteRegistersPost [2, 23, 22, 19, 8, 1, 25, 24, 21, 20, 18, 9] [] c ra 1#64
        [(2, sp), (23, s7), (22, s6), (19, s3), (8, s0), (1, ra), (25, s9), (24, s8), (21, s5), (20, s4), (18, s2),
          (9, s1), (10, 1#64)]) := by
  have savedRa := saved 88 ra (by simp [fsInitRestored])
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (fs_init_part_0X04a8FSeg ++ fs_init_part_0X04c4Seg) 0x800004a8#64
        [(21, 0#64), (22, table), (2, nativeStack sp 96), (10, 1#64)] (fsReturnLoads c.σ.mem sp table) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [21, 22, 2, 10]; decide
      shape := by change ChainOK _ [21, 22, 2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := fsInitNext_code leaf.image
        chain_facts code with "Vsa.Sim.Code.fs_init_part_0_at_"
        · exact endW.ld rfl (by
            simp only [fsinitnext_line_800004a8, fsinitnext_line_800004ac, fsinitnext_line_800004b0, fsinitnext_line_800004b4, fsinitnext_line_800004b8, fsinitnext_line_800004bc, fsinitreturn_line_800004c4, fsinitreturn_line_800004c8, fsinitreturn_line_800004cc, fsinitreturn_line_800004d0, fsinitreturn_line_800004d4, fsinitreturn_line_800004d8, fsinitreturn_line_800004dc, fsinitreturn_line_800004e0, fsinitreturn_line_800004e4, fsinitreturn_line_800004e8, fsinitreturn_line_800004ec, fsinitreturn_line_800004f0, eaddrM, srcVal, lookupG, runGM, stepGM, eraseG, wvalM, Option.getD_some, ite_true,
              ite_false, imm20Of, Nat.reduceEqDiff, shamtOf]
            rw [next_entry_offset, show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide, BitVec.add_zero])
            (read8_pins _ _)
        · change guardB bop.BNE (bytesVal .ld (read8 c.σ.mem (table + 24#64).toNat)) 0#64 = false
          rw [read8_value, ended]
          decide
        · exact (frame.read_slot (off := 72) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 64) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 48) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 16) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 88) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 80) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 56) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl (by restore_addr)
            (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 96 + 88)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 96 + 88)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · simp only [fs_init_part_0X04a8FSeg, fs_init_part_0X04c4Seg, evalBlocks, evalBlock, SegEvalState.init, fsinitnext_line_800004a8, fsinitnext_line_800004ac, fsinitnext_line_800004b0, fsinitnext_line_800004b4, fsinitnext_line_800004b8, fsinitnext_line_800004bc, fsinitreturn_line_800004c4, fsinitreturn_line_800004c8, fsinitreturn_line_800004cc, fsinitreturn_line_800004d0, fsinitreturn_line_800004d4, fsinitreturn_line_800004d8, fsinitreturn_line_800004dc, fsinitreturn_line_800004e0, fsinitreturn_line_800004e4, fsinitreturn_line_800004e8, fsinitreturn_line_800004ec, fsinitreturn_line_800004f0, runGM,
      ldsRunM, wlogM, stepGM, stepLdsM, eaddrM, srcVal, lookupG, eraseG, wvalM, wentryM, widthOfM, List.headD_cons,
      List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false, fsReturnLoads, List.map_cons,
      List.map_nil, read8_value, List.cons_append, List.nil_append]
    rw [show Functions.sign_extend (m := 64) 96#12 = 96#64 by decide, nativeStack_restore, savedRa, saved 24 s7 (by simp [fsInitRestored]), saved 32 s6 (by simp [fsInitRestored]), saved 56 s3 (by simp [fsInitRestored]), saved 80 s0 (by simp [fsInitRestored]), saved 8 s9 (by simp [fsInitRestored]), saved 16 s8 (by simp [fsInitRestored]), saved 40 s5 (by simp [fsInitRestored]), saved 48 s4 (by simp [fsInitRestored]), saved 64 s2 (by simp [fsInitRestored]), saved 72 s1 (by simp [fsInitRestored])]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
