import OCaml.Vm.Boot.Startup.GcMessageQuietNormalized
import OCaml.Vm.Boot.Startup.GcMessageQuietImage
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.FindRestore
import OCaml.Vm.Boot.Startup.StrncmpReturn
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-! `caml_gc_message(level, fmt, ...)` with `caml_verb_gc = 0`: the variadic
prologue spills a2–a7 and ra, the level test fails, and it returns. -/

def gcMessageSlots (ra a2 a3 a4 a5 a6 a7 : BitVec 64) : List (Nat × BitVec 64) :=
  [(24, ra), (32, a2), (40, a3), (48, a4), (56, a5), (64, a6), (72, a7)]
def gcMessageLog (sp ra a2 a3 a4 a5 a6 a7 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 (gcMessageSlots ra a2 a3 a4 a5 a6 a7)
def gcMessageInput (sp ra a2 a3 a4 a5 a6 a7 a0 : BitVec 64) : GRegs :=
  [(2, sp), (1, ra), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6), (17, a7), (10, a0)]

theorem gcMessageLog_inside {sp ra a2 a3 a4 a5 a6 a7} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (gcMessageLog sp ra a2 a3 a4 a5 a6 a7) := by
  apply frame.word_log_inside
  intro off value member
  simp only [gcMessageSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

theorem gc_message_save (c : Config) (sp ra a2 a3 a4 a5 a6 a7 a0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (gcMessageInput sp ra a2 a3 a4 a5 a6 a7 a0))
    (quiet : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)) :
    FnSummary 0x80003cb0#64 (fun d => d = c)
      (WriteRegistersPost [6, 2, 10] (gcMessageLog sp ra a2 a3 a4 a5 a6 a7) c 0x80003ce0#64 0#64
        [(10, 0#64), (2, nativeStack sp 80), (6, 0#64), (1, ra), (12, a2), (13, a3), (14, a4), (15, a5),
          (16, a6), (17, a7)]) := by
  apply registers_of_blocks leaf.image (frame.image_outside (gcMessageLog_inside frame))
    (block_summary _ _ _ _ _ (show BlockInput caml_gc_messageX3cb0FSeg 0x80003cb0#64
        (gcMessageInput sp ra a2 a3 a4 a5 a6 a7 a0) [List.replicate 8 0#8] c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 1, 12, 13, 14, 15, 16, 17, 10]; decide
      shape := by change ChainOK _ [2, 1, 12, 13, 14, 15, 16, 17, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := gcMessageQuiet_code leaf.image
        have slot (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
            WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 8 := by
          rw [nativeStack, frame.address _ (by omega)]
          exact frame.word bound aligned
        chain_facts code with "Vsa.Sim.Code.caml_gc_message_at_"
        · apply ReadWindow.ld (x := BitVec.ofNat 64 Layout.sym_caml_verb_gc) (by constructor <;> decide) rfl
          · simp only [gcmessagequiet_line_80003cb0, gcmessagequiet_line_80003cb4, eaddrM, srcVal, lookupG,
              stepGM, eraseG, wvalM, Option.getD_some, ite_true, ite_false, imm20Of, Nat.reduceEqDiff]
            decide
          exact quiet
        · exact (slot 24 (by decide) (by decide)).sd rfl rfl
        · exact (slot 32 (by decide) (by decide)).sd rfl rfl
        · exact (slot 40 (by decide) (by decide)).sd rfl rfl
        · exact (slot 48 (by decide) (by decide)).sd rfl rfl
        · exact (slot 56 (by decide) (by decide)).sd rfl rfl
        · exact (slot 64 (by decide) (by decide)).sd rfl rfl
        · exact (slot 72 (by decide) (by decide)).sd rfl rfl
        · change guardB bop.BNE (a0 &&& bytesVal .ld (List.replicate 8 0#8)) 0#64 = false
          rw [show bytesVal .ld (List.replicate 8 0#8) = 0#64 from by decide, BitVec.and_zero]
          rfl }))
  · rfl
  · rfl
  · change [(10, a0 &&& bytesVal .ld (List.replicate 8 0#8)), (2, nativeStack sp 80),
      (6, bytesVal .ld (List.replicate 8 0#8)), (1, ra), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6),
      (17, a7)] = _
    rw [show bytesVal .ld (List.replicate 8 0#8) = 0#64 from by decide, BitVec.and_zero]
  · rfl
  · decide

def gcMessageReturnLoads (sp : BitVec 64) (c : Config) : List (List (BitVec 8)) :=
  [read8 c.σ.mem (nativeFrameBase sp 80 + 24)]

theorem gc_message_return (c : Config) (sp ra oldra v : BitVec 64) (leaf : LeafInput oldra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ [(2, nativeStack sp 80), (10, v)])
    (savedRa : bytesT c.σ.mem (nativeFrameBase sp 80 + 24) 8 = ra) (aligned : ra.toNat % 4 = 0) :
    FnSummary 0x80003ce0#64 (fun d => d = c)
      (WriteRegistersPost [1, 2] [] c ra v [(2, sp), (1, ra), (10, v)]) := by
  apply registers_of_blocks leaf.image (by constructor <;> trivial)
    (block_summary _ _ _ _ _ (show BlockInput caml_gc_messageX3ce0Seg 0x80003ce0#64
        [(2, nativeStack sp 80), (10, v)] (gcMessageReturnLoads sp c) c from {
      good := leaf.good
      minstret := leaf.minstret
      regs := regs
      keys := by change KeysOK [2, 10]; decide
      shape := by change ChainOK _ [2, 10] _; decide
      tick := leaf.tick
      facts := by
        have code := gcMessageQuiet_code leaf.image
        chain_facts code with "Vsa.Sim.Code.caml_gc_message_at_"
        · exact (frame.read_slot (off := 24) (by decide) (by decide)).ld rfl rfl (frame.pins_slot c (by decide))
        · change (Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 24)) +
            Functions.sign_extend (m := 64) 0#12) 0 0#1).toNat % 4 = 0
          rw [read8_value, savedRa, ret_tgt ra aligned]
          exact aligned }))
  · rfl
  · change Sail.BitVec.update (bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 24)) +
      Functions.sign_extend (m := 64) 0#12) 0 0#1 = _
    rw [read8_value, savedRa, ret_tgt ra aligned]
  · change [(2, nativeStack sp 80 + 80#64), (1, bytesVal .ld (read8 c.σ.mem (nativeFrameBase sp 80 + 24))),
      (10, v)] = _
    rw [read8_value, savedRa, show nativeStack sp 80 + 80#64 = sp from nativeStack_restore sp 80]
  · rfl
  · decide

/-- `caml_gc_message` at verbosity zero spills its variadic arguments and returns. -/
theorem gc_message_quiet (c : Config) (sp ra a2 a3 a4 a5 a6 a7 a0 : BitVec 64) (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (gcMessageInput sp ra a2 a3 a4 a5 a6 a7 a0))
    (quiet : LPins8 c.σ.mem Layout.sym_caml_verb_gc (List.replicate 8 0#8)) :
    FnSummary 0x80003cb0#64 (fun d => d = c)
      (WriteRegistersPost [6, 2, 10, 1] (gcMessageLog sp ra a2 a3 a4 a5 a6 a7) c ra 0#64
        [(2, sp), (1, ra), (10, 0#64), (6, 0#64)]) := by
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨a, run1, saved⟩ := (gc_message_save c sp ra a2 a3 a4 a5 a6 a7 a0 leaf frame regs quiet).run c ⟨pc, rfl⟩
  have savedRa : bytesT a.σ.mem (nativeFrameBase sp 80 + 24) 8 = ra := by
    rw [saved.memory]
    apply frame.word_log_read (slots := gcMessageSlots ra a2 a3 a4 a5 a6 a7)
    · intro k v hk
      simp only [gcMessageSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hk
      omega
    · simp [gcMessageSlots]
    · simp [gcMessageSlots]
  obtain ⟨after, run2, returned⟩ := (gc_message_return a sp ra ra 0#64 (saved.leaf (by rfl) leaf.aligned) frame
    ⟨gholds_lookup (n := 2) _ saved.regs (by rfl), gholds_lookup (n := 10) _ saved.regs (by rfl), trivial⟩
    savedRa leaf.aligned).run a ⟨saved.pc, rfl⟩
  have effects := (saved.toEffectPost.trans returned.toEffectPost).widen (writes' := [6, 2, 10, 1]) (by decide)
  exact ⟨after, run1.trans run2, ⟨{ effects with memory := returned.memory.trans saved.memory },
    gholds_lookup (n := 2) _ returned.regs (by rfl), gholds_lookup (n := 1) _ returned.regs (by rfl),
    gholds_lookup (n := 10) _ returned.regs (by rfl),
    (returned.frame .x6 (by decide) (by decide)).trans (gholds_lookup (n := 6) _ saved.regs (by rfl)), trivial⟩⟩
end OCaml.Vm.Boot.Startup
