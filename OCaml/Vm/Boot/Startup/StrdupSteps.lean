import OCaml.Vm.Boot.Startup.StrdupAllocNormalized
import OCaml.Vm.Boot.Startup.StrdupAllocCallInterface
import OCaml.Vm.Boot.Startup.StrdupCopyNormalized
import OCaml.Vm.Boot.Startup.StrdupCopyCallInterface
import OCaml.Vm.Boot.Startup.StrdupReturnNormalized
import OCaml.Vm.Boot.Startup.StrdupReturnImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import OCaml.Vm.Boot.Startup.PrefixCall
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def strdupSizeLog (sp size : BitVec 64) : List WEntry := [((nativeStack sp 48 + 8#64).toNat, 8, size)]
def strdupAllocArgs (sp size : BitVec 64) : GRegs := [(10, size), (12, size), (2, nativeStack sp 48)]

theorem strdupSizeLog_inside {sp size} (frame : NativeFrame sp 48) :
    LogInW [⟨nativeFrameBase sp 48, sp.toNat⟩] (strdupSizeLog sp size) := by
  have address := frame.slot_nat (off := 8) (by decide)
  have lower := frame.lower
  simp only [strdupSizeLog, nativeStack, frame.address 8 (by decide), address, LogInW, InsideW]
  exact ⟨Or.inl ⟨by omega, by unfold nativeFrameBase; omega⟩, trivial⟩

/-- Store `len + 1` and call `caml_stat_alloc_noexc` with it. -/
theorem strdup_alloc_call (c : Config) (sp len ra : BitVec 64) (leaf : LeafInput ra c) (frame : NativeFrame sp 48)
    (regs : GHolds c.σ [(10, len), (2, nativeStack sp 48)]) :
    FnSummary 0x8000be0c#64 (fun d => d = c)
      (WriteRegistersPost [12, 10, 1] (strdupSizeLog sp (len + 1#64)) c jal_8000be18_call.target (len + 1#64)
        ((1, jal_8000be18_call.link) :: strdupAllocArgs sp (len + 1#64))) := by
  have front : FnSummary 0x8000be0c#64 (fun d => d = c)
      (WriteRegistersPost [12, 10] (strdupSizeLog sp (len + 1#64)) c jal_8000be18_call.pc (len + 1#64)
        (strdupAllocArgs sp (len + 1#64))) := by
    apply registers_of_blocks leaf.image (frame.image_outside (strdupSizeLog_inside frame))
      (block_summary _ _ _ _ _ (show BlockInput strdupAllocSave 0x8000be0c#64 [(10, len), (2, nativeStack sp 48)] [] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 2]; decide
        shape := by change ChainOK _ [10, 2] _; decide
        tick := leaf.tick
        facts := by
          have code := strdupAlloc_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_stat_strdup_at_"
          have window : WriteWindow (nativeStack sp 48 + 8#64) 8 := by
            rw [nativeStack, frame.address 8 (by decide)]
            exact frame.word (by decide) (by decide)
          exact window.sd rfl rfl }))
    · change [((nativeStack sp 48 + 8#64).toNat, 8, len + 1#64)] = _
      rfl
    · rfl
    · change [(10, len + 1#64 + 0#64), (12, len + 1#64), (2, nativeStack sp 48)] = _
      rw [BitVec.add_zero]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_8000be18_call_shape jal_8000be18_call_decode request
    (jal_8000be18_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [10, 12, 2]; decide) (by simp only [KeysAvoidRa, strdupAllocArgs, keysG]; decide)
    (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩

def strdupCopyArgs (sp p size name : BitVec 64) : GRegs :=
  [(8, p), (11, name), (12, size), (10, p), (2, nativeStack sp 48), (9, name)]

/-- Reload the size, check the fresh buffer and call `memcpy(p, name, size)`. -/
theorem strdup_copy_call (c : Config) (sp p size name ra : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(10, p), (2, nativeStack sp 48), (9, name)])
    (nonzero : p ≠ 0#64) (saved : bytesT c.σ.mem (nativeFrameBase sp 48 + 8) 8 = size) :
    FnSummary 0x8000be1c#64 (fun d => d = c)
      (WriteRegistersPost [12, 11, 8, 1] [] c jal_8000be2c_call.target p
        ((1, jal_8000be2c_call.link) :: strdupCopyArgs sp p size name)) := by
  have front : FnSummary 0x8000be1c#64 (fun d => d = c)
      (WriteRegistersPost [12, 11, 8] [] c jal_8000be2c_call.pc p (strdupCopyArgs sp p size name)) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (show BlockInput (caml_stat_strdupXbe1cFSeg ++ strdupCopySave) 0x8000be1c#64
          [(10, p), (2, nativeStack sp 48), (9, name)] [read8 c.σ.mem (nativeFrameBase sp 48 + 8)] c from {
        good := leaf.good
        minstret := leaf.minstret
        regs := regs
        keys := by change KeysOK [10, 2, 9]; decide
        shape := by change ChainOK _ [10, 2, 9] _; decide
        tick := leaf.tick
        facts := by
          have code := strdupCopy_code leaf.image
          chain_facts code with "Vsa.Sim.Code.caml_stat_strdup_at_"
          · exact (frame.read_slot (off := 8) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
          · exact beq_eq_false_iff_ne.mpr nonzero }))
    · rfl
    · rfl
    · change [(8, p + 0#64), (11, name + 0#64), (12, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 8))),
        (10, p), (2, nativeStack sp 48), (9, name)] = _
      rw [BitVec.add_zero, BitVec.add_zero, read8_value, saved]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_8000be2c_call_shape jal_8000be2c_call_decode request
    (jal_8000be2c_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [8, 11, 12, 10, 2, 9]; decide) (by simp only [KeysAvoidRa, strdupCopyArgs, keysG]; decide)
    (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩

def strdupReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 48 + 40), read8 c.σ.mem (nativeFrameBase sp 48 + 32),
   read8 c.σ.mem (nativeFrameBase sp 48 + 24)]

/-- Restore the caller and return the copy. -/
theorem strdup_return (c : Config) (sp ra s0 s1 p oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 48) (regs : GHolds c.σ [(2, nativeStack sp 48), (8, p)])
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 48 + 40) 8 = ra)
    (savedS0 : bytesT c.σ.mem (nativeFrameBase sp 48 + 32) 8 = s0)
    (savedS1 : bytesT c.σ.mem (nativeFrameBase sp 48 + 24) 8 = s1) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x8000be30#64 (fun d => d = c)
      (WriteRegistersPost [1, 10, 8, 9, 2] [] c ra p [(2, sp), (9, s1), (8, s0), (10, p), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_stat_strdupXbe30Seg 0x8000be30#64
        [(2, nativeStack sp 48), (8, p)] (strdupReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 8]; decide
      shape := by change ChainOK _ [2, 8] _; decide
      tick := leaf.tick
      facts := by
        have code := strdupReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_stat_strdup_at_"
        · exact (frame.read_slot (off := 40) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 32) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · change [(2, nativeStack sp 48 + 48#64), (9, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 24))),
      (8, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 32))), (10, p + 0#64),
      (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 48 + 40)))] = _
    rw [read8_value, read8_value, read8_value, savedRa, savedS0, savedS1, BitVec.add_zero, nativeStack_restore]
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
