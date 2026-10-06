import OCaml.Vm.Sim.EntryPrep
import OCaml.Vm.Sim.InterpEntryResumeSegment
import OCaml.Vm.Sim.InterpEntryResumePins

/-!
# caml_interprete's entry, part 4: the zero-result resume

`entry_resume` runs `tr_interp_entry_resume` after `setjmp` returned 0: it
publishes `Caml_state->external_raise = &raise_buf` and loads the initial VM
registers (pc = prog, sp = extern_sp, env = Atom(0), accu = Val_int 0,
extra_args = 0) before LOOP_SETUP.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The resume's single store. -/
def entryResumeLog (sp : Nat) (c : Config) : List WEntry :=
  [((word c Layout.sym_Caml_state).toNat + Layout.off_external_raise, 8,
    BitVec.ofNat 64 (sp - Layout.interpFrameBytes + 208))]

structure EntryResumeInput (c : Config) (sp : Nat) : Prop where
  good : GoodState c.σ
  image : ExecutableImage c
  tick : c.tick < 2
  pc : pcOf c = some 0x80001e80#64
  result : gpr c 10 = some 0#64
  stack : gpr c 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  frame : EntryFrame sp
  domain : DomainWindow (word c Layout.sym_Caml_state).toNat

structure EntryResumePost (before : Config) (sp : Nat) (after : Config) : Prop where
  good : GoodState after.σ
  image : ExecutableImage after
  tick : after.tick < 2
  pc : pcOf after = some 0x80001f40#64
  vmPc : gpr after 8 = some (word before (sp - Layout.interpFrameBytes + 16))
  vmSp : gpr after 9 = some (domainField before Layout.off_extern_sp)
  accu : gpr after 21 = some 1#64
  extra : gpr after 18 = some 0#64
  env : gpr after 25 = some (word before Layout.sym_caml_atom_table + 8#64)
  stack : gpr after 2 = some (BitVec.ofNat 64 (sp - Layout.interpFrameBytes))
  memory : after.σ.mem = writeLog before.σ.mem (entryResumeLog sp before)
  output : after.σ.sailOutput = before.σ.sailOutput
  htif : after.σ.regs.get? Register.htif_payload_writes = before.σ.regs.get? Register.htif_payload_writes
  gprs : OCaml.Vm.Boot.Startup.GprPresent before.σ → OCaml.Vm.Boot.Startup.GprPresent after.σ

theorem entry_resume {c : Config} {sp : Nat} (h : EntryResumeInput c sp) :
    ∃ n after, StepsN n c after ∧ EntryResumePost c sp after := by
  obtain ⟨b1, b2, b3⟩ := h.frame.nat
  obtain ⟨d1, d2, d3⟩ := h.domain.nat
  have symD : (((0x80001e80#64) + (sign_extend (m := 64) ((0x00063#20) +++ 0x000#12))) +
      sign_extend (m := 64) (0xe88#12)) + sign_extend (m := 64) (0x000#12) =
        BitVec.ofNat 64 Layout.sym_Caml_state := by decide
  have symA : ((0x80001f1c#64) + (sign_extend (m := 64) ((0x00063#20) +++ 0x000#12))) +
      sign_extend (m := 64) (0xa84#12) = BitVec.ofNat 64 Layout.sym_caml_atom_table := by decide
  have mD : Layout.sym_Caml_state % 18446744073709551616 = Layout.sym_Caml_state := by decide
  have mA : Layout.sym_caml_atom_table % 18446744073709551616 = Layout.sym_caml_atom_table := by decide
  have hb : (BitVec.ofNat 64 (sp - Layout.interpFrameBytes)).toNat = sp - 528 :=
    Nat.mod_eq_of_lt (by simp only [Layout.interpFrameBytes]; omega)
  have hd : (word c Layout.sym_Caml_state).toNat = (word c Layout.sym_Caml_state).toNat := rfl
  have bp : SegSt (0x80001e80#64) [⟨Register.x10, 0#64⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - Layout.interpFrameBytes)⟩]
      (fun σ => Vsa.Sim.Code.CamlInterpEntryResumeLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, h.pc, ⟨h.result, h.stack, trivial⟩, h.good.minstret, h.tick,
      interp_entry_resume_loaded h.image, rfl, rfl⟩
  have wordRead (a : Nat) : word c a = sign_extend (m := 64) (bytesT8 c.σ.mem a) := by
    simp only [word, bytesT_eight_eq, sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have run := tr_interp_entry_resume 0#64 (BitVec.ofNat 64 (sp - Layout.interpFrameBytes)) c.σ.mem c.σ
  simp only [symD, symA, BitVec.toNat_ofNat, Nat.reducePow, mD, mA] at run
  have run := run (by slot_tac) (by slot_tac) (by slot_tac) (word c Layout.sym_Caml_state)
    (wordRead _) (by decide)
    (by slot_tac) (by slot_tac) (by slot_tac) (word c Layout.sym_caml_atom_table) (wordRead _)
  simp (disch := decide) only [addr_pos _ _ hd (by omega), addr_pos _ _ hb (by omega),
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at run
  have buf : BitVec.ofNat 64 (sp - Layout.interpFrameBytes) + sign_extend (m := 64) (0x0d0#12) =
      BitVec.ofNat 64 (sp - Layout.interpFrameBytes + 208) := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_pos _ _ hb (by omega) _ (by decide), BitVec.toNat_ofNat]
    simp only [Layout.interpFrameBytes]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp only [buf] at run
  obtain ⟨n, after, _, steps, post⟩ := run
    (by slot_tac) (by slot_tac) (by slot_tac) (domainField c Layout.off_extern_sp) (wordRead _)
    (by slot_tac) (by slot_tac) (by slot_tac) (word c (sp - Layout.interpFrameBytes + 16)) (wordRead _)
    (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac) (by slot_tac)
    (writeLog c.σ.mem (entryResumeLog sp c)) rfl c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have one : (0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12) = 1#64 := by decide
  have zero : (0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  have eight : sign_extend (m := 64) (0x008#12) = 8#64 := by decide
  have accu : gpr after 21 = some ((0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12)) :=
    PinsHold.get post.pins ⟨0, by simp⟩
  have extra : gpr after 18 = some ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) :=
    PinsHold.get post.pins ⟨1, by simp⟩
  have env : gpr after 25 = some (word c Layout.sym_caml_atom_table + sign_extend (m := 64) (0x008#12)) :=
    PinsHold.get post.pins ⟨2, by simp⟩
  rw [one] at accu; rw [zero] at extra; rw [eight] at env
  refine ⟨n, after, steps, post.good, image_of_writeLog h.image ?_ memory, post.tick, post.pcAt,
    PinsHold.get post.pins ⟨4, by simp⟩, PinsHold.get post.pins ⟨5, by simp⟩, accu, extra, env,
    PinsHold.get post.pins ⟨8, by simp⟩, memory, frame.out, frame.frame _ (by decide),
    fun p => p.of_stepFrame frame (writes := [21, 18, 25, 14, 8, 9, 15, 10]) (by decide) (by decide +kernel)
      (written_of_pins post.pins (by simp [gprReg]))⟩
  constructor <;>
    simp only [OutLRange, entryResumeLog, Layout.off_external_raise, Image.textBase, Image.textSize,
      Image.rodataBase, Image.rodataSize, and_true] <;> omega

end OCaml.Vm.Sim
