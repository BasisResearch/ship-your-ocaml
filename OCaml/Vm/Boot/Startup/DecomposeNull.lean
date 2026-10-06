import OCaml.Vm.Boot.Startup.DecomposeNullNormalized
import OCaml.Vm.Boot.Startup.DecomposeNullImage
import OCaml.Vm.Boot.Startup.DecomposeReturnNormalized
import OCaml.Vm.Boot.Startup.DecomposeReturnImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def decomposeLog (sp ra s2 : BitVec 64) : List WEntry := nativeWordLog sp 32 [(24, ra), (0, s2)]
def decomposeInput (sp ra s2 tbl : BitVec 64) : GRegs := [(2, sp), (1, ra), (18, s2), (11, 0#64), (10, tbl)]
def decomposeSaved (sp ra s2 tbl : BitVec 64) : GRegs :=
  [(2, nativeStack sp 32), (1, ra), (18, s2), (11, 0#64), (10, tbl)]

theorem decomposeLog_inside {sp ra s2} (frame : NativeFrame sp 32) :
    LogInW [⟨nativeFrameBase sp 32, sp.toNat⟩] (decomposeLog sp ra s2) := by
  apply frame.word_log_inside
  intro off value member
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

theorem decompose_save (c : Config) (sp ra s2 tbl : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ (decomposeInput sp ra s2 tbl)) :
    FnSummary 0x80025340#64 (fun d => d = c)
      (WriteRegistersPost [2] (decomposeLog sp ra s2) c 0x800253ec#64 tbl (decomposeSaved sp ra s2 tbl)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (decomposeLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput caml_decompose_pathX5340TSeg 0x80025340#64
        (decomposeInput sp ra s2 tbl) [] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 18, 11, 10]; decide
      shape := by change ChainOK _ [2, 1, 18, 11, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := decomposeNull_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 32) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 32 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_decompose_path_at_"
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 0 (by decide) (by decide)).sd rfl rfl
        · rfl }))
  · rfl
  · rfl
  · rfl
  · rfl
  · decide

def decomposeReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 32 + 24), read8 c.σ.mem (nativeFrameBase sp 32 + 0)]

theorem decompose_return (c : Config) (sp ra s2 oldra : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 32) (stack : gprGet c.σ 2 = some (nativeStack sp 32))
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 32 + 24) 8 = ra)
    (savedS2 : bytesT c.σ.mem (nativeFrameBase sp 32 + 0) 8 = s2) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x800253ec#64 (fun d => d = c)
      (WriteRegistersPost [1, 18, 10, 2] [] c ra 0#64 [(2, sp), (18, s2), (10, 0#64), (1, ra)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_decompose_pathX53ecSeg 0x800253ec#64
        [(2, nativeStack sp 32)] (decomposeReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := ⟨stack, trivial⟩
      keys := by change KeysOK [2]; decide
      shape := by change ChainOK _ [2] _; decide
      tick := leaf.tick
      facts := by
        have code := decomposeReturn_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_decompose_path_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · exact (frame.read_slot (off := 0) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · change [(2, nativeStack sp 32 + 32#64), (18, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 0))),
      (10, 0#64 + 0#64 + 0#64), (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 32 + 24)))] = _
    rw [read8_value, read8_value, savedRa, savedS2, show nativeStack sp 32 + 32#64 = sp from nativeStack_restore sp 32]
    rfl
  · rfl
  · decide

/-- `caml_decompose_path(tbl, NULL)` saves, finds no path and returns NULL. -/
theorem decompose_null (c : Config) (sp ra s2 tbl : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 32) (regs : GHolds c.σ (decomposeInput sp ra s2 tbl)) :
    FnSummary 0x80025340#64 (fun d => d = c)
      (WriteRegistersPost [2, 1, 18, 10] (decomposeLog sp ra s2) c ra 0#64
        [(2, sp), (18, s2), (10, 0#64), (1, ra)]) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, saved⟩ := (decompose_save c sp ra s2 tbl leaf frame regs).run c ⟨pc, rfl⟩
  have read (off : Nat) (value : BitVec 64) (member : (off, value) ∈ [(24, ra), (0, s2)]) :
      bytesT a.σ.mem (nativeFrameBase sp 32 + off) 8 = value := by
    rw [saved.memory]
    apply frame.word_log_read (slots := [(24, ra), (0, s2)])
    · intro k v hk
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp
    · exact member
  obtain ⟨after, run2, returned⟩ := (decompose_return a sp ra s2 ra (saved.leaf (by rfl) leaf.aligned) frame
    (gholds_lookup (n := 2) _ saved.regs (by rfl)) (read 24 ra (by simp)) (read 0 s2 (by simp))
    leaf.aligned).run a ⟨saved.pc, rfl⟩
  have effects := (saved.toEffectPost.trans returned.toEffectPost).widen (writes' := [2, 1, 18, 10]) (by decide)
  exact ⟨after, run1.trans run2, ⟨{ effects with memory := returned.memory.trans saved.memory }, returned.regs⟩⟩
end OCaml.Vm.Boot.Startup
