import OCaml.Vm.Boot.Startup.SearchInPathPrefixNormalized
import OCaml.Vm.Boot.Startup.SearchInPathPrefixImage
import OCaml.Vm.Boot.Startup.SearchInPathFirstNormalized
import OCaml.Vm.Boot.Startup.SearchInPathFirstImage
import OCaml.Vm.Boot.Startup.SearchInPathScanNormalized
import OCaml.Vm.Boot.Startup.SearchInPathScanImage
import OCaml.Vm.Boot.Startup.SearchInPathEmptyNormalized
import OCaml.Vm.Boot.Startup.SearchInPathEmptyImage
import OCaml.Vm.Boot.Startup.SearchInPathDupNormalized
import OCaml.Vm.Boot.Startup.SearchInPathDupCallInterface
import OCaml.Vm.Boot.Startup.SearchInPathReturnNormalized
import OCaml.Vm.Boot.Startup.SearchInPathReturnImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.NameByte
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Word32Access
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def searchInPathLog (sp ra s0 s2 s3 : BitVec 64) : List WEntry :=
  nativeWordLog sp 176 [(144, s2), (136, s3), (168, ra), (160, s0)]
def searchInPathInput (sp ra s0 s2 s3 tbl name : BitVec 64) : GRegs :=
  [(2, sp), (18, s2), (19, s3), (1, ra), (8, s0), (10, tbl), (11, name)]
def searchInPathSaved (sp ra s0 s2 s3 tbl name : BitVec 64) : GRegs :=
  [(2, nativeStack sp 176), (18, s2), (19, s3), (1, ra), (8, s0), (10, tbl), (11, name)]

theorem searchInPathLog_inside {sp ra s0 s2 s3} (frame : NativeFrame sp 176) :
    LogInW [⟨nativeFrameBase sp 176, sp.toNat⟩] (searchInPathLog sp ra s0 s2 s3) := by
  apply frame.word_log_inside
  intro off value member
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

/-- caml_search_in_path's four saves. -/
theorem search_in_path_prefix (c : Config) (sp ra s0 s2 s3 tbl name : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 176) (regs : GHolds c.σ (searchInPathInput sp ra s0 s2 s3 tbl name)) :
    FnSummary 0x80025404#64 (fun d => d = c)
      (WriteRegistersPost [2] (searchInPathLog sp ra s0 s2 s3) c 0x80025418#64 tbl
        (searchInPathSaved sp ra s0 s2 s3 tbl name)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (searchInPathLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput caml_search_in_pathX5404Seg 0x80025404#64
        (searchInPathInput sp ra s0 s2 s3 tbl name) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 18, 19, 1, 8, 10, 11]; decide
      shape := by change ChainOK _ [2, 18, 19, 1, 8, 10, 11] _; decide
      tick := leaf.tick
      facts := by
        have code := searchInPathPrefix_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 176) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 176 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
        · exact (slot 144 (by decide) (by decide)).sd rfl rfl
        · exact (slot 136 (by decide) (by decide)).sd rfl rfl
        · exact (slot 168 (by decide) (by decide)).sd rfl rfl
        · exact (slot 160 (by decide) (by decide)).sd rfl rfl }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def searchInPathScanRegs (tbl name cursor : BitVec 64) (b : BitVec 8) : GRegs :=
  [(13, 47#64), (14, cursor), (18, tbl), (19, name), (15, nameByteWord b)]

/-- Load the first character; a nonempty name enters the slash scan. -/
theorem search_in_path_first (c : Config) (ra tbl name : BitVec 64) (b : BitVec 8) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(11, name), (10, tbl)]) (window : ReadWindow name 1)
    (pin : (c.σ.mem[name.toNat]?).getD 0 = b) (nonzero : b ≠ 0#8) :
    FnSummary 0x80025418#64 (fun d => d = c)
      (WriteRegistersPost [15, 19, 18, 14, 13] [] c 0x8002543c#64 tbl
        (searchInPathScanRegs tbl name name b ++ [(11, name), (10, tbl)])) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput (caml_search_in_pathX5418FSeg ++ caml_search_in_pathX5428Seg)
        0x80025418#64 [(11, name), (10, tbl)] [[b]] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [11, 10]; decide
      shape := by change ChainOK _ [11, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := searchInPathFirst_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
        · exact window.lbu rfl (BitVec.add_zero name) pin
        · change (bytesVal .lbu [b] == 0#64) = false
          rw [name_lbu_value]
          refine beq_eq_false_iff_ne.mpr (fun h => nonzero ?_)
          apply BitVec.eq_of_toNat_eq
          have := congrArg BitVec.toNat h
          simp only [nameByteWord, BitVec.toNat_setWidth] at this
          have := b.isLt
          simp only [BitVec.toNat_ofNat] at *
          omega }))
  · rfl
  · rfl
  · change [(13, 0#64 + 47#64), (14, name + 0#64), (18, tbl + 0#64), (19, name + 0#64),
      (15, bytesVal .lbu [b]), (11, name), (10, tbl)] = _
    rw [name_lbu_value, BitVec.add_zero, BitVec.add_zero, BitVec.zero_add]
    rfl
  · rfl
  · decide

def scanStepInput (cursor : BitVec 64) (b : BitVec 8) (a0 : BitVec 64) : GRegs :=
  [(14, cursor), (15, nameByteWord b), (13, 47#64), (10, a0)]

/-- One slash-scan step: the current character is not `/`; load the next. -/
theorem search_scan_step (c : Config) (ra cursor a0 : BitVec 64) (b next : BitVec 8) (stop : Bool)
    (leaf : LeafInput ra c) (regs : GHolds c.σ (scanStepInput cursor b a0)) (notSlash : b ≠ 47#8)
    (window : ReadWindow (cursor + 1#64) 1) (pin : (c.σ.mem[(cursor + 1#64).toNat]?).getD 0 = next)
    (zero : next = 0#8 ↔ stop = true) :
    FnSummary 0x8002543c#64 (fun d => d = c)
      (WriteRegistersPost [14, 15] [] c (if stop then 0x8002546c#64 else 0x8002543c#64) a0
        [(15, nameByteWord next), (14, cursor + 1#64), (13, 47#64), (10, a0)]) := by
  have neSlash : nameByteWord b ≠ 47#64 := nameByteWord_ne_of notSlash (by decide)
  cases stop
  · have nz : next ≠ 0#8 := fun h => by simpa using zero.mp h
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (caml_search_in_pathX543cTSeg ++ caml_search_in_pathX5434FSeg)
          0x8002543c#64 (scanStepInput cursor b a0) [[next]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [14, 15, 13, 10]; decide
        shape := by change ChainOK _ [14, 15, 13, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := searchInPathScan_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
          · exact bne_iff_ne.mpr neSlash
          · exact window.lbu rfl (by change cursor + 1#64 + 0#64 = _; rw [BitVec.add_zero]) pin
          · change (bytesVal .lbu [next] == 0#64) = false
            rw [name_lbu_value]
            exact beq_eq_false_iff_ne.mpr (nameByteWord_ne_of nz (by decide)) }))
    · rfl
    · rfl
    · change [(15, bytesVal .lbu [next]), (14, cursor + 1#64), (13, 47#64), (10, a0)] = _
      rw [name_lbu_value]
    · rfl
    · decide
  · have z : next = 0#8 := zero.mpr rfl
    subst z
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (caml_search_in_pathX543cTSeg ++ caml_search_in_pathX5434TSeg)
          0x8002543c#64 (scanStepInput cursor b a0) [[0#8]] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [14, 15, 13, 10]; decide
        shape := by change ChainOK _ [14, 15, 13, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := searchInPathScan_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
          · exact bne_iff_ne.mpr neSlash
          · exact window.lbu rfl (by change cursor + 1#64 + 0#64 = _; rw [BitVec.add_zero]) pin
          · rfl }))
    · rfl
    · rfl
    · rfl
    · rfl
    · decide

/-- An empty path table falls through to `caml_stat_strdup(name)`. -/
theorem search_in_path_dup (c : Config) (ra tbl name a0 : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ [(18, tbl), (19, name), (10, a0)]) (window : ReadWindow tbl 4)
    (size : LPins4 c.σ.mem tbl.toNat (List.replicate 4 0#8)) :
    FnSummary 0x8002546c#64 (fun d => d = c)
      (WriteRegistersPost [15, 10, 1] [] c jal_80025448_call.target name
        [(1, jal_80025448_call.link), (10, name), (15, 0#64), (18, tbl), (19, name)]) := by
  have front : FnSummary 0x8002546c#64 (fun d => d = c)
      (WriteRegistersPost [15, 10] [] c jal_80025448_call.pc name [(10, name), (15, 0#64), (18, tbl), (19, name)]) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (caml_search_in_pathX546cTSeg ++ searchInPathDupSave) 0x8002546c#64
          [(18, tbl), (19, name), (10, a0)] [List.replicate 4 0#8] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [18, 19, 10]; decide
        shape := by change ChainOK _ [18, 19, 10] _; decide
        tick := leaf.tick
        facts := by
          have code := searchInPathEmpty_code leaf.image
          have dup := searchInPathDup_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
          · exact window.lw rfl (by change tbl + 0#64 = tbl; rw [BitVec.add_zero]) size
          · rfl }))
    · rfl
    · rfl
    · change [(10, name + 0#64), (15, bytesVal .lw (List.replicate 4 0#8)), (18, tbl), (19, name)] = _
      rw [BitVec.add_zero, show bytesVal .lw (List.replicate 4 0#8) = 0#64 from by decide]
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_80025448_call_shape jal_80025448_call_decode request
    (jal_80025448_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [10, 15, 18, 19]; decide) (by simp only [KeysAvoidRa, keysG]; decide)
    (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩

def searchInPathReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 176 + 168), read8 c.σ.mem (nativeFrameBase sp 176 + 160),
   read8 c.σ.mem (nativeFrameBase sp 176 + 144), read8 c.σ.mem (nativeFrameBase sp 176 + 136)]

/-- Restore the caller and return the found or duplicated name. -/
theorem search_in_path_return (c : Config) (sp ra s0 s2 s3 p oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 176) (regs : GHolds c.σ [(10, p), (2, nativeStack sp 176)])
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 176 + 168) 8 = ra)
    (savedS0 : bytesT c.σ.mem (nativeFrameBase sp 176 + 160) 8 = s0)
    (savedS2 : bytesT c.σ.mem (nativeFrameBase sp 176 + 144) 8 = s2)
    (savedS3 : bytesT c.σ.mem (nativeFrameBase sp 176 + 136) 8 = s3) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8002544c#64 (fun d => d = c)
      (WriteRegistersPost [8, 1, 10, 18, 19, 2] [] c ra p
        [(2, sp), (19, s3), (18, s2), (8, s0), (10, p), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_search_in_pathX544cSeg 0x8002544c#64
        [(10, p), (2, nativeStack sp 176)] (searchInPathReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [10, 2]; decide
      shape := by change ChainOK _ [10, 2] _; decide
      tick := leaf.tick
      facts := by
        have code := searchInPathReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_search_in_path_at_"
        · exact (frame.read_slot (off := 168) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 160) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 144) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 136) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 168)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 168)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · change [(2, nativeStack sp 176 + 176#64), (19, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 136))),
      (18, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 144))),
      (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 160))), (10, p + 0#64 + 0#64),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 176 + 168)))] = _
    rw [read8_value, read8_value, read8_value, read8_value, savedRa, savedS0, savedS2, savedS3,
      BitVec.add_zero, BitVec.add_zero, nativeStack_restore]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
