import OCaml.Vm.Boot.Startup.SeekOptionalAdjustNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalAdjustImage
import OCaml.Vm.Boot.Startup.SeekOptionalSaveNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalSaveImage
import OCaml.Vm.Boot.Startup.SeekOptionalRestoreLinkNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalRestoreLinkImage
import OCaml.Vm.Boot.Startup.SeekOptionalRestoreBankNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalRestoreBankImage
import OCaml.Vm.Boot.Startup.SeekOptionalReloadNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalReloadImage
import OCaml.Vm.Boot.Startup.SeekOptionalEntryNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalEntryImage
import OCaml.Vm.Boot.Startup.SeekOptionalSetupNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalSetupImage
import OCaml.Vm.Boot.Startup.SeekOptionalCompareNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalCompareImage
import OCaml.Vm.Boot.Startup.SeekOptionalTestNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalTestImage
import OCaml.Vm.Boot.Startup.SeekOptionalNextNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalNextImage
import OCaml.Vm.Boot.Startup.SeekOptionalFoundNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalFoundImage
import OCaml.Vm.Boot.Startup.SeekOptionalReturnNormalized
import OCaml.Vm.Boot.Startup.SeekOptionalReturnImage
import OCaml.Vm.Boot.Startup.SeekOptionalCompareCallInterface
import OCaml.Vm.Boot.Startup.SeekOptionalFoundCallInterface
import OCaml.Vm.Boot.Startup.SeekCodeReset

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

abbrev seekStack : BitVec 64 := nativeStack parameterStack 64

theorem seek_frame : NativeFrame parameterStack 64 := by constructor <;> decide

def seekHeadSlots (saved : Nat → BitVec 64) : List (Nat × BitVec 64) :=
  [(40,saved 9),(56,0x80004ea8#64),(32,saved 18)]
def seekTailSlots (saved : Nat → BitVec 64) : List (Nat × BitVec 64) :=
  [(24,saved 19),(16,saved 20),(8,saved 21),(0,saved 22),(48,3#64)]
def seekHeadLog (saved : Nat → BitVec 64) := nativeWordLog parameterStack 64 (seekHeadSlots saved)
def seekTailLog (saved : Nat → BitVec 64) := nativeWordLog parameterStack 64 (seekTailSlots saved)
def seekSaveLog (saved : Nat → BitVec 64) := seekHeadLog saved ++ seekTailLog saved

theorem seekHeadLog_inside (saved : Nat → BitVec 64) :
    LogInW [⟨nativeFrameBase parameterStack 64,parameterStack.toNat⟩] (seekHeadLog saved) :=
  seek_frame.word_log_inside fun off value hm => by
    simp only [seekHeadSlots,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm; omega

theorem seekTailLog_inside (saved : Nat → BitVec 64) :
    LogInW [⟨nativeFrameBase parameterStack 64,parameterStack.toNat⟩] (seekTailLog saved) :=
  seek_frame.word_log_inside fun off value hm => by
    simp only [seekTailSlots,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hm; omega

local macro "seek_nf" : tactic => `(tactic| simp only [
  seekoptionalentry_line_80004bcc, seekoptionalentry_line_80004bd0, seekoptionalentry_line_80004bd4, seekoptionalentry_line_80004bd8,
  seekoptionalentry_line_80004bdc, seekoptionalentry_line_80004be0, seekoptionalsetup_line_80004be8, seekoptionalsetup_line_80004bec,
  seekoptionalsetup_line_80004bf0, seekoptionalsetup_line_80004bf4, seekoptionalsetup_line_80004bf8, seekoptionalsetup_line_80004bfc,
  seekoptionalsetup_line_80004c00, seekoptionalsetup_line_80004c04, seekoptionalsetup_line_80004c08, seekoptionalsetup_line_80004c0c,
  seekoptionalsetup_line_80004c10, seekoptionalsetup_line_80004c14, seekoptionalsetup_line_80004c18, seekoptionalsetup_line_80004c1c,
  seekoptionalsetup_line_80004c20, seekoptionalcompare_line_80004c34, seekoptionalcompare_line_80004c38, seekoptionalcompare_line_80004c3c,
  seekoptionalcompare_line_80004c40, seekoptionalcompare_line_80004c44, seekoptionaltest_line_80004c4c, seekoptionalnext_line_80004c28,
  seekoptionalnext_line_80004c2c, seekoptionalfound_line_80004c54, seekoptionalfound_line_80004c58, seekoptionalfound_line_80004c5c,
  seekoptionalreturn_line_80004c64, seekoptionalreturn_line_80004c68, seekoptionalreturn_line_80004c6c, seekoptionalreturn_line_80004c70,
  seekoptionalreturn_line_80004c74, seekoptionalreturn_line_80004c78, seekoptionalreturn_line_80004c7c, seekoptionalreturn_line_80004c80,
  seekoptionalreturn_line_80004c84, seekoptionalreturn_line_80004c88, seekoptionalreturn_line_80004c8c, seekoptionalreturn_line_80004c90,
  runGM,ldsRunM,wlogM,stepGM,stepLdsM,stepMemM,eaddrM,srcVal,lookupG,eraseG,
  wvalM,wentryM,widthOfM,List.headD_cons,List.tail_cons,Option.getD_some,
  Nat.reduceEqDiff,ite_true,ite_false,BitVec.add_zero])

/-- Adjust the native stack before any saved-bank store. -/
theorem seek_optional_adjust (c : Config) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004ea8#64 c)
    (regs : GHolds c.σ [(2,parameterStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
      (11,WhileMinElfParse.trailSlot),(10,3#64)]) :
    FnSummary 0x80004bcc#64 (fun d => d = c)
      (WriteRegistersPost [2] [] c 0x80004bd0#64 3#64
        [(2,seekStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
          (11,WhileMinElfParse.trailSlot),(10,3#64)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4bccSeg 0x80004bcc#64
        [(2,parameterStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
          (11,WhileMinElfParse.trailSlot),(10,3#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,9,1,18,11,10]; decide
      shape := by change ChainOK _ [2,9,1,18,11,10] _; decide
      facts := by
        have code := seekOptionalAdjust_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_" }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- First three native saves and the actual nonempty-table branch. -/
theorem seek_optional_save (c : Config) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004ea8#64 c)
    (regs : GHolds c.σ [(2,seekStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
      (11,WhileMinElfParse.trailSlot),(10,3#64)])
    (count : read4 c.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord) :
    FnSummary 0x80004bd0#64 (fun d => d = c)
      (WriteRegistersPost [9,18] (seekHeadLog saved) c 0x80004be8#64 3#64
        [(9,6#64),(18,7#64),(2,seekStack),(1,0x80004ea8#64),
          (11,WhileMinElfParse.trailSlot),(10,3#64)]) := by
  apply registers_of_blocks leaf.image (seek_frame.image_outside (seekHeadLog_inside saved))
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4bd0FSeg 0x80004bd0#64
        [(2,seekStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
          (11,WhileMinElfParse.trailSlot),(10,3#64)] [sectionsWord] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,9,1,18,11,10]; decide
      shape := by change ChainOK _ [2,9,1,18,11,10] _; decide
      facts := by
        have code := seekOptionalSave_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ |
            refine memFacts_stepMem_store rfl ?_ (fun _ => by
              seek_nf; simp only [OutLRange,and_true]; decide))
          exact (show ReadWindow WhileMinElfParse.trailSlot 4 by constructor <;> decide).lw
            rfl (by seek_nf; rfl) (by rw [← count]; exact read4_pins _ _)
        · seek_nf
          decide }))
  · simp only [caml_seek_optional_sectionX4bd0FSeg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rfl
  · rfl
  · simp only [caml_seek_optional_sectionX4bd0FSeg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rfl
  · rfl
  · decide

/-- Execute the bounded adjustment and save/count regions at the real optional entry. -/
theorem seek_optional_entry (c : Config) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004ea8#64 c)
    (regs : GHolds c.σ [(2,parameterStack),(9,saved 9),(1,0x80004ea8#64),(18,saved 18),
      (11,WhileMinElfParse.trailSlot),(10,3#64)])
    (count : read4 c.σ.mem WhileMinElfParse.trailSlot.toNat = sectionsWord) :
    FnSummary 0x80004bcc#64 (fun d => d = c)
      (WriteRegistersPost [2,9,18] (seekHeadLog saved) c 0x80004be8#64 3#64
        [(9,6#64),(18,7#64),(2,seekStack),(1,0x80004ea8#64),
          (11,WhileMinElfParse.trailSlot),(10,3#64)]) := by
  apply blocks_then c (seek_optional_adjust c saved leaf regs)
  intro d P
  exact seek_optional_save d saved (P.leaf rfl (by decide)) P.regs
    (by rw [show d.σ.mem = c.σ.mem from P.memory]; exact count)

/-- Save the remaining callee bank and enter the reverse loop at its last descriptor. -/
theorem seek_optional_setup (c : Config) (saved : Nat → BitVec 64) (blk : BitVec 64)
    (leaf : LeafInput 0x80004ea8#64 c)
    (regs : GHolds c.σ [(19,saved 19),(2,seekStack),(20,saved 20),(21,saved 21),(22,saved 22),
      (8,3#64),(11,WhileMinElfParse.trailSlot),(18,7#64),(9,6#64),(12,codeSectionName0),(10,3#64)])
    (table : bytesT c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk) :
    FnSummary 0x80004be8#64 (fun d => d = c)
      (WriteRegistersPost [8,18,19,20,21,22] (seekTailLog saved) c 0x80004c34#64 3#64
        [(8,blk + 48#64),(18,72#64),(21,WhileMinElfParse.trailSlot),(22,3#64),
          (20,codeSectionName0),(19,48#64),(2,seekStack),(11,WhileMinElfParse.trailSlot),
          (9,6#64),(12,codeSectionName0),(10,3#64)]) := by
  apply registers_of_blocks leaf.image (seek_frame.image_outside (seekTailLog_inside saved))
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4be8Seg 0x80004be8#64
        [(19,saved 19),(2,seekStack),(20,saved 20),(21,saved 21),(22,saved 22),
          (8,3#64),(11,WhileMinElfParse.trailSlot),(18,7#64),(9,6#64),(12,codeSectionName0),(10,3#64)]
        [read8 c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [19,2,20,21,22,8,11,18,9,12,10]; decide
      shape := by change ChainOK _ [19,2,20,21,22,8,11,18,9,12,10] _; decide
      facts := by
        have code := seekOptionalSetup_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · seek_nf
          exact (show WriteWindow _ 8 by constructor <;> (seek_nf; decide)).sd rfl rfl
        · repeat (first | refine memFacts_stepMem_skip rfl ?_ |
            refine memFacts_stepMem_store rfl ?_ (fun _ => by
              seek_nf; simp only [OutLRange,and_true]; decide))
          exact (show ReadWindow (WhileMinElfParse.trailSlot + 16#64) 8 by constructor <;> decide).ld
            rfl (by seek_nf; rfl) (read8_pins _ _)
        }))
  · simp only [caml_seek_optional_sectionX4be8Seg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rfl
  · rfl
  · simp only [caml_seek_optional_sectionX4be8Seg,evalBlocks,evalBlock,SegEvalState.init,
      List.cons_append,List.nil_append]
    seek_nf
    rw [read8_value, table]
    rfl
  · rfl
  · decide

/-- Unsigned word loads use the same total-byte RAM window as signed loads. -/
theorem seek_lwu_facts {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : ReadWindow x 4)
    (kind : a.kind = .lwu) (address : eaddrM a L = x) (pins : LPins4 m x.toNat bs) :
    MemFacts m L bs a := by
  simp only [MemFacts,kind,address]
  refine ⟨⟨h.lower,h.upper,?_⟩,pins⟩
  simpa only [tohostAddr,LibraryLayout.tohostAddr,Layout.sym_tohost] using h.htif

/-- The loop's real unsigned length load, accumulation and four-byte call. -/
theorem seek_optional_compare (c : Config) (ra p offset length total : BitVec 64)
    (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(8,p),(18,offset),(20,codeSectionName0)])
    (window : ReadWindow (p + 4#64) 4)
    (loaded : bytesVal .lwu (read4 c.σ.mem (p + 4#64).toNat) = length)
    (add : offset + length = total) :
    FnSummary 0x80004c34#64 (fun d => d = c)
      (WriteRegistersPost ([15,12,11,10,18] ++ [1]) [] c 0x80040cc8#64 p
        [(1,0x80004c4c#64),(18,total),(10,p),(11,codeSectionName0),(12,4#64),
          (15,length),(8,p),(20,codeSectionName0)]) := by
  apply block_then_call c jal_80004c48_call_shape jal_80004c48_call_decode
    (fun _ h => jal_80004c48_call_pins h) ?_ (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa,keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4c34Seg 0x80004c34#64
        [(8,p),(18,offset),(20,codeSectionName0)] [read4 c.σ.mem (p + 4#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [8,18,20]; decide
      shape := by change ChainOK _ [8,18,20] _; decide
      facts := by
        have code := seekOptionalCompare_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        exact seek_lwu_facts window rfl (by seek_nf; rfl) (read4_pins _ _) }))
  · rfl
  · rfl
  · simp only [caml_seek_optional_sectionX4c34Seg,evalBlocks,evalBlock,SegEvalState.init,
      List.cons_append,List.nil_append]
    seek_nf
    rw [show Functions.sign_extend (m := 64) 4#12 = 4#64 by decide,loaded,add,
      show Functions.sign_extend (m := 64) 0#12 = 0#64 by decide]
    simp only [BitVec.add_zero,BitVec.zero_add]
  · rfl
  · decide

def seekCountDown (count : BitVec 64) : BitVec 64 :=
  Functions.sign_extend (m := 64) (Sail.BitVec.extractLsb (count + (-1#64)) 31 0)

/-- A nonmatching descriptor takes the real back edge and advances both cursors. -/
theorem seek_optional_next (c : Config) (p off count result ra : BitVec 64)
    (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9,count),(10,result),(19,off),(8,p)])
    (nonzero : result ≠ 0#64)
    (nonnegative : guardB bop.BLT
      (seekCountDown count) 0#64 = false) :
    FnSummary 0x80004c4c#64 (fun d => d = c)
      (WriteRegistersPost [9,19,8] [] c 0x80004c34#64 result
        [(8,p + (-8#64)),(19,off + (-8#64)),
          (9,seekCountDown count),(10,result)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput
        (caml_seek_optional_sectionX4c4cTSeg ++ caml_seek_optional_sectionX4c28FSeg) 0x80004c4c#64
        [(9,count),(10,result),(19,off),(8,p)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [9,10,19,8]; decide
      shape := by change ChainOK _ [9,10,19,8] _; decide
      facts := by
        have code := seekOptionalTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · exact bne_iff_ne.mpr nonzero
        · seek_nf
          rw [show Functions.sign_extend (m := 64) 0xfff#12 = -1#64 by decide]
          exact nonnegative }))
  · rfl
  · rfl
  · simp only [caml_seek_optional_sectionX4c4cTSeg,caml_seek_optional_sectionX4c28FSeg,
      evalBlocks,evalBlock,SegEvalState.init,List.cons_append,List.nil_append]
    seek_nf
    rw [show Functions.sign_extend (m := 64) 0xfff#12 = -1#64 by decide,
      show Functions.sign_extend (m := 64) 0xff8#12 = -8#64 by decide]
    rfl
  · rfl
  · decide

/-- Equal CODE name: the actual test falls through and calls lseek(3,-9331,2). -/
theorem seek_optional_found (c : Config) (ra : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(9,0#64),(10,0#64),(18,9331#64),(22,3#64)]) :
    FnSummary 0x80004c4c#64 (fun d => d = c)
      (WriteRegistersPost ([9,11,10,12] ++ [1]) [] c 0x80042574#64 3#64
        [(1,0x80004c64#64),(12,2#64),(10,3#64),(11,0#64 - 9331#64),(9,-1#64),
          (18,9331#64),(22,3#64)]) := by
  apply block_then_call c jal_80004c60_call_shape jal_80004c60_call_decode
    (fun _ h => jal_80004c60_call_pins h) ?_ (by simp only [keysG]; decide)
    (by simp only [KeysAvoidRa,keysG]; decide) rfl
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput
        (caml_seek_optional_sectionX4c4cFSeg ++ caml_seek_optional_sectionX4c54Seg) 0x80004c4c#64
        [(9,0#64),(10,0#64),(18,9331#64),(22,3#64)] [] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [9,10,18,22]; decide
      shape := by change ChainOK _ [9,10,18,22] _; decide
      facts := by
        have code := seekOptionalTest_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        decide }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

/-- The saved words consumed by the native epilogue, in its load order. -/
def seekRestoreSlots (saved : Nat → BitVec 64) : List (Nat × BitVec 64) :=
  [(48,3#64),(24,saved 19),(16,saved 20),(8,saved 21),(0,saved 22),(56,0x80004ea8#64),(40,saved 9),(32,saved 18)]

/-- Reload the current table pointer and its signed CODE length before restoring registers. -/
theorem seek_optional_reload (c : Config) (blk : BitVec 64)
    (leaf : LeafInput 0x80004c64#64 c)
    (regs : GHolds c.σ [(21,WhileMinElfParse.trailSlot),(19,0#64),(2,seekStack)])
    (table : bytesT c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk)
    (window : ReadWindow (blk + 4#64) 4)
    (length : bytesVal .lw (read4 c.σ.mem (blk + 4#64).toNat) = 764#64) :
    FnSummary 0x80004c64#64 (fun d => d = c)
      (WriteRegistersPost [15,10] [] c 0x80004c70#64 764#64
        [(10,764#64),(15,blk),(21,WhileMinElfParse.trailSlot),(19,0#64),(2,seekStack)]) := by
  have pointer : bytesVal .ld (read8 c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat) = blk :=
    (read8_value _ _).trans table
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_reloadX4c64Seg 0x80004c64#64
        [(21,WhileMinElfParse.trailSlot),(19,0#64),(2,seekStack)]
        [read8 c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat,
          read4 c.σ.mem (blk + 4#64).toNat] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [21,19,2]; decide
      shape := by change ChainOK _ [21,19,2] _; decide
      facts := by
        have code := seekOptionalReload_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · exact (show ReadWindow (WhileMinElfParse.trailSlot + 16#64) 8 by
            constructor <;> decide).ld rfl (by seek_nf; rfl) (read8_pins _ _)
        · refine window.lw rfl ?_ (read4_pins _ _)
          seek_nf
          rw [pointer]
          rfl }))
  · rfl
  · rfl
  · simp only [caml_seek_optional_reloadX4c64Seg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rw [pointer,length]
  · rfl
  · decide

/-- Restore the actual saved words in the bounded RestoreBank region. -/
theorem seek_optional_restorebank (c : Config) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004c64#64 c) (regs : GHolds c.σ [(2,seekStack),(10,764#64)])
    (savedWords : ∀ off value, (off,value) ∈ seekRestoreSlots saved →
      bytesT c.σ.mem (seekStack.toNat + off) 8 = value) :
    FnSummary 0x80004c70#64 (fun d => d = c)
      (WriteRegistersPost [8,19,20,21,22] [] c 0x80004c84#64 764#64
        [(22,saved 22),(21,saved 21),(20,saved 20),(19,saved 19),(8,3#64),(2,seekStack),(10,764#64)]) := by
  have word (off : Nat) (value : BitVec 64) (hm : (off,value) ∈ seekRestoreSlots saved) :
      bytesVal .ld (read8 c.σ.mem (seekStack.toNat + off)) = value := by
    rw [read8_value,savedWords off value hm]
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4c70Seg 0x80004c70#64
        [(2,seekStack),(10,764#64)] [read8 c.σ.mem (seekStack.toNat + 48),
          read8 c.σ.mem (seekStack.toNat + 24),
          read8 c.σ.mem (seekStack.toNat + 16),
          read8 c.σ.mem (seekStack.toNat + 8),
          read8 c.σ.mem (seekStack.toNat + 0)] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,10]; decide
      shape := by change ChainOK _ [2,10] _; decide
      facts := by
        have code := seekOptionalRestoreBank_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · exact (seek_frame.read_slot (off := 48) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 16) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
 }))
  · rfl
  · rfl
  · simp only [caml_seek_optional_sectionX4c70Seg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rw [word 48 (3#64) (by simp [seekRestoreSlots])]
    rw [word 24 (saved 19) (by simp [seekRestoreSlots])]
    rw [word 16 (saved 20) (by simp [seekRestoreSlots])]
    rw [word 8 (saved 21) (by simp [seekRestoreSlots])]
    rw [word 0 (saved 22) (by simp [seekRestoreSlots])]
  · rfl
  · decide

/-- Restore the actual saved words in the bounded RestoreLink region. -/
theorem seek_optional_restorelink (c : Config) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004c64#64 c) (regs : GHolds c.σ [(2,seekStack),(10,764#64)])
    (savedWords : ∀ off value, (off,value) ∈ seekRestoreSlots saved →
      bytesT c.σ.mem (seekStack.toNat + off) 8 = value) :
    FnSummary 0x80004c84#64 (fun d => d = c)
      (WriteRegistersPost [1,9,18,2] [] c 0x80004ea8#64 764#64
        [(2,parameterStack),(18,saved 18),(9,saved 9),(1,0x80004ea8#64),(10,764#64)]) := by
  have word (off : Nat) (value : BitVec 64) (hm : (off,value) ∈ seekRestoreSlots saved) :
      bytesVal .ld (read8 c.σ.mem (seekStack.toNat + off)) = value := by
    rw [read8_value,savedWords off value hm]
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_seek_optional_sectionX4c84Seg 0x80004c84#64
        [(2,seekStack),(10,764#64)] [read8 c.σ.mem (seekStack.toNat + 56),
          read8 c.σ.mem (seekStack.toNat + 40),
          read8 c.σ.mem (seekStack.toNat + 32)] c from {
      good := leaf.good
      minstret := leaf.minstret
      tick := leaf.tick
      regs := regs
      keys := by change KeysOK [2,10]; decide
      shape := by change ChainOK _ [2,10] _; decide
      facts := by
        have code := seekOptionalRestoreLink_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_seek_optional_section_at_"
        · exact (seek_frame.read_slot (off := 56) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · exact (seek_frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl
            (seek_frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (seekStack.toNat + 56)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [word 56 0x80004ea8#64 (by simp [seekRestoreSlots])]
          decide }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (seekStack.toNat + 56)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = 0x80004ea8#64
    rw [word 56 0x80004ea8#64 (by simp [seekRestoreSlots])]
    decide
  · simp only [caml_seek_optional_sectionX4c84Seg,evalBlocks,evalBlock,SegEvalState.init]
    seek_nf
    rw [word 56 (0x80004ea8#64) (by simp [seekRestoreSlots])]
    rw [word 40 (saved 9) (by simp [seekRestoreSlots])]
    rw [word 32 (saved 18) (by simp [seekRestoreSlots])]
    rfl
  · rfl
  · decide

/-- The bounded epilogue summaries restore the original caller and return signed length 764. -/
theorem seek_optional_return (c : Config) (blk : BitVec 64) (saved : Nat → BitVec 64)
    (leaf : LeafInput 0x80004c64#64 c)
    (regs : GHolds c.σ [(21,WhileMinElfParse.trailSlot),(19,0#64),(2,seekStack)])
    (table : bytesT c.σ.mem (WhileMinElfParse.trailSlot + 16#64).toNat 8 = blk)
    (window : ReadWindow (blk + 4#64) 4)
    (length : bytesVal .lw (read4 c.σ.mem (blk + 4#64).toNat) = 764#64)
    (savedWords : ∀ off value, (off,value) ∈ seekRestoreSlots saved →
      bytesT c.σ.mem (seekStack.toNat + off) 8 = value) :
    FnSummary 0x80004c64#64 (fun d => d = c)
      (WriteRegistersPost [15,10,8,19,20,21,22,1,9,18,2] [] c 0x80004ea8#64 764#64
        [(2,parameterStack),(18,saved 18),(9,saved 9),(1,0x80004ea8#64),(22,saved 22),
          (21,saved 21),(20,saved 20),(19,saved 19),(8,3#64),(10,764#64),(15,blk)]) := by
  constructor
  rintro before ⟨pc,eq⟩
  subst before
  obtain ⟨a,runA,A⟩ := (seek_optional_reload c blk leaf regs table window length).run c ⟨pc,rfl⟩
  have gA := GprsSame.of_post A (by decide)
  have leafA : LeafInput 0x80004c64#64 a := ⟨A.good,A.image,A.minstret,
    gA.get (by decide) (by decide) (by decide) leaf.raReg,leaf.aligned,A.tick⟩
  obtain ⟨b,runB,B⟩ := (seek_optional_restorebank a saved leafA
    ⟨gholds_lookup (n := 2) _ A.regs rfl,A.result,trivial⟩
    (fun off value hm => by rw [show a.σ.mem = c.σ.mem from A.memory]; exact savedWords off value hm)).run a ⟨A.pc,rfl⟩
  have gB := GprsSame.of_post B (by decide)
  have leafB : LeafInput 0x80004c64#64 b := ⟨B.good,B.image,B.minstret,
    gB.get (by decide) (by decide) (by decide) leafA.raReg,leaf.aligned,B.tick⟩
  obtain ⟨after,runC,C⟩ := (seek_optional_restorelink b saved leafB
    ⟨gholds_lookup (n := 2) _ B.regs rfl,B.result,trivial⟩
    (fun off value hm => by rw [show b.σ.mem = c.σ.mem from B.memory.trans A.memory]; exact savedWords off value hm)).run b ⟨B.pc,rfl⟩
  have gC := GprsSame.of_post C (by decide)
  have post := write_post_seq A (write_post_seq B C)
  refine ⟨after,runA.trans (runB.trans runC),⟨post.toEffectPost.widen (by decide),
    gholds_lookup (n := 2) _ C.regs rfl,gholds_lookup (n := 18) _ C.regs rfl,
    gholds_lookup (n := 9) _ C.regs rfl,gholds_lookup (n := 1) _ C.regs rfl,
    gC.get (by decide) (by decide) (by decide) (gholds_lookup (n := 22) _ B.regs rfl),
    gC.get (by decide) (by decide) (by decide) (gholds_lookup (n := 21) _ B.regs rfl),
    gC.get (by decide) (by decide) (by decide) (gholds_lookup (n := 20) _ B.regs rfl),
    gC.get (by decide) (by decide) (by decide) (gholds_lookup (n := 19) _ B.regs rfl),
    gC.get (by decide) (by decide) (by decide) (gholds_lookup (n := 8) _ B.regs rfl),
    C.result,(gB.trans gC).get (by decide) (by decide) (by decide)
      (gholds_lookup (n := 15) _ A.regs rfl),trivial⟩⟩

/-- Read-only scan blocks and comparisons retain the same selected runtime ledger. -/
theorem seek_readonly_ready {H capacity oldsp oldra before after writes pc value regs sp ra}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes [] before pc value regs after)
    (keys : KeysOK writes) (no3 : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra)
    (aligned : ra.toNat % 4 = 0) : RuntimeReady H capacity sp ra after :=
  ready.stack_log_written post keys
    (fun n _ lo hi => post.kept.present n lo hi (ready.platform.gpr n lo (by omega)))
    no3 stack link aligned seek_frame (by simp only [LogInW])

end OCaml.Vm.Boot.Startup
