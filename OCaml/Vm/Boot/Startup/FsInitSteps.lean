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
end OCaml.Vm.Boot.Startup
