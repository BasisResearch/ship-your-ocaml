import OCaml.Vm.Boot.Startup.AttemptOpenPrefixNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenPrefixImage
import OCaml.Vm.Boot.Startup.AttemptOpenNameNormalized
import OCaml.Vm.Boot.Startup.AttemptOpenNameCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Write
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- caml_attempt_open's six callee saves. -/
def attemptOpenSlots (ra s0 s1 s2 s3 s4 : BitVec 64) : List (Nat × BitVec 64) :=
  [(56, ra), (48, s0), (40, s1), (32, s2), (24, s3), (16, s4)]
def attemptOpenLog (sp ra s0 s1 s2 s3 s4 : BitVec 64) : List WEntry :=
  nativeWordLog sp 64 (attemptOpenSlots ra s0 s1 s2 s3 s4)

def attemptOpenInput (sp ra s0 s1 s2 s3 s4 name : BitVec 64) : GRegs :=
  [(2, sp), (1, ra), (8, s0), (9, s1), (18, s2), (19, s3), (20, s4), (10, name)]
def attemptOpenSaved (sp ra s0 s1 s2 s4 name : BitVec 64) : GRegs :=
  [(19, name), (2, nativeStack sp 64), (1, ra), (8, s0), (9, s1), (18, s2), (20, s4), (10, name)]
/-- Entering caml_search_exe_in_path: a0 = `*name`, s3 = `name`, s0 = `trail`,
s4 = `do_open_script`. -/
def attemptOpenNameInput (sp s1 s2 name trail flag : BitVec 64) : GRegs :=
  [(10, name), (11, trail), (12, flag), (19, name), (2, nativeStack sp 64), (9, s1), (18, s2)]
def attemptOpenRegs (sp s1 s2 name trail flag value : BitVec 64) : GRegs :=
  [(20, flag), (8, trail), (10, value), (11, trail), (12, flag), (19, name), (2, nativeStack sp 64),
    (9, s1), (18, s2)]

theorem attemptOpenLog_inside {sp ra s0 s1 s2 s3 s4} (frame : NativeFrame sp 64) :
    LogInW [⟨nativeFrameBase sp 64, sp.toNat⟩] (attemptOpenLog sp ra s0 s1 s2 s3 s4) := by
  apply frame.word_log_inside
  intro off value member
  simp only [attemptOpenSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  omega

theorem attemptOpen_image_outside {sp ra s0 s1 s2 s3 s4} (frame : NativeFrame sp 64) :
    ImageOutside (attemptOpenLog sp ra s0 s1 s2 s3 s4) := by
  have lower := frame.lower
  have bounds : Image.textBase + Image.textSize ≤ Vsa.Sim.DlHeap.heapEnd ∧
      Image.rodataBase + Image.rodataSize ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  constructor
  all_goals apply OCaml.Vm.Sim.outLRange_of_windows (attemptOpenLog_inside frame)
  all_goals exact ⟨Or.inl (by change _ ≤ nativeFrameBase sp 64; unfold nativeFrameBase; omega), trivial⟩

theorem attemptOpenSave_input {sp ra s0 s1 s2 s3 s4 name c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 64) (regs : GHolds c.σ (attemptOpenInput sp ra s0 s1 s2 s3 s4 name)) :
    BlockInput caml_attempt_openX48c0Seg 0x800048c0#64 (attemptOpenInput sp ra s0 s1 s2 s3 s4 name) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 1, 8, 9, 18, 19, 20, 10]; decide
  shape := by change ChainOK _ [2, 1, 8, 9, 18, 19, 20, 10] _; decide
  tick := leaf.tick
  facts := by
    have code := attemptOpenPrefix_code leaf.image
    have slot (off : Nat) (bound : off + 8 ≤ 64) (aligned : off % 8 = 0) :
        WriteWindow (nativeStack sp 64 + BitVec.ofNat 64 off) 8 := by
      rw [nativeStack, frame.address _ (by omega)]
      exact frame.word bound aligned
    chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
    · exact (slot 56 (by decide) (by decide)).sd rfl rfl
    · exact (slot 48 (by decide) (by decide)).sd rfl rfl
    · exact (slot 40 (by decide) (by decide)).sd rfl rfl
    · exact (slot 32 (by decide) (by decide)).sd rfl rfl
    · exact (slot 24 (by decide) (by decide)).sd rfl rfl
    · exact (slot 16 (by decide) (by decide)).sd rfl rfl

theorem attempt_open_save (c : Config) (sp ra s0 s1 s2 s3 s4 name : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 64)
    (regs : GHolds c.σ (attemptOpenInput sp ra s0 s1 s2 s3 s4 name)) :
    FnSummary 0x800048c0#64 (fun d => d = c)
      (WriteRegistersPost [2, 19] (attemptOpenLog sp ra s0 s1 s2 s3 s4) c 0x800048e0#64 name
        (attemptOpenSaved sp ra s0 s1 s2 s4 name)) := by
  apply registers_of_blocks leaf.image (attemptOpen_image_outside frame)
    (block_summary _ _ _ _ _ (attemptOpenSave_input leaf frame regs))
  · rfl
  · rfl
  · change [(19, name + 0#64), (2, nativeStack sp 64), (1, ra), (8, s0), (9, s1), (18, s2), (20, s4),
      (10, name)] = _
    rw [BitVec.add_zero]
    rfl
  · rfl
  · decide

theorem attemptOpenName_input {ra sp s1 s2 name trail flag c} (leaf : LeafInput ra c)
    (regs : GHolds c.σ (attemptOpenNameInput sp s1 s2 name trail flag)) (load : ReadWindow name 8) :
    BlockInput attemptOpenNameSave 0x800048e0#64 (attemptOpenNameInput sp s1 s2 name trail flag)
      [read8 c.σ.mem name.toNat] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [10, 11, 12, 19, 2, 9, 18]; decide
  shape := by change ChainOK _ [10, 11, 12, 19, 2, 9, 18] _; decide
  tick := leaf.tick
  facts := by
    have code := attemptOpenName_code leaf.image
    chain_facts code with "Vsa.Sim.Code.caml_attempt_open_at_"
    exact load.ld rfl (by change name + 0#64 = name; rw [BitVec.add_zero]) (read8_pins _ _)

/-- Load `*name` and call caml_search_exe_in_path. -/
theorem attempt_open_name (c : Config) (ra sp s1 s2 name trail flag : BitVec 64) (leaf : LeafInput ra c)
    (regs : GHolds c.σ (attemptOpenNameInput sp s1 s2 name trail flag)) (load : ReadWindow name 8) :
    FnSummary 0x800048e0#64 (fun d => d = c)
      (WriteRegistersPost [20, 8, 10, 1] [] c jal_800048ec_call.target (bytesT c.σ.mem name.toNat 8)
        ((1, jal_800048ec_call.link) ::
          attemptOpenRegs sp s1 s2 name trail flag (bytesT c.σ.mem name.toNat 8))) := by
  have front : FnSummary 0x800048e0#64 (fun d => d = c)
      (WriteRegistersPost [20, 8, 10] [] c jal_800048ec_call.pc (bytesT c.σ.mem name.toNat 8)
        (attemptOpenRegs sp s1 s2 name trail flag (bytesT c.σ.mem name.toNat 8))) := by
    apply registers_of_blocks leaf.image (by constructor <;> trivial)
      (block_summary _ _ _ _ _ (attemptOpenName_input leaf regs load))
    · rfl
    · rfl
    · change [(20, flag + 0#64), (8, trail + 0#64), (10, bytesVal .ld (read8 c.σ.mem name.toNat)),
        (11, trail), (12, flag), (19, name), (2, nativeStack sp 64), (9, s1), (18, s2)] = _
      rw [BitVec.add_zero, BitVec.add_zero, read8_value]
      rfl
    · rfl
    · decide
  constructor
  intro before ⟨pc, eq⟩
  subst before
  obtain ⟨request, run1, setup⟩ := front.run c ⟨pc, rfl⟩
  obtain ⟨after, run2, called⟩ := (call_registers_summary jal_800048ec_call_shape jal_800048ec_call_decode request
    (jal_800048ec_call_pins setup.image) setup.good setup.image setup.tick setup.minstret _ setup.regs
    (by change KeysOK [20, 8, 10, 11, 12, 19, 2, 9, 18]; decide)
    (by simp only [KeysAvoidRa, attemptOpenRegs, keysG]; decide) (by rfl)).run request ⟨setup.pc, rfl⟩
  exact ⟨after, run1.trans run2, prefix_call_post setup called⟩
end OCaml.Vm.Boot.Startup
