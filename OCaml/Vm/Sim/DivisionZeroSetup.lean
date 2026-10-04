import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.DivisionZeroSetupState
import OCaml.Vm.Sim.DivisionZeroSetupSegment
import OCaml.Vm.Sim.DivisionZeroSetupPins
import Vsa.Sim.FnSummary

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Native stack adjustment expressed as the shared bytecode frame address. -/
theorem division_zero_env_sp (sp : BitVec 64) :
    sp + sign_extend (m := 64) (0xff8#12) = divisionZeroEnvSp sp := by
  rw [show sign_extend (m := 64) (0xff8#12) = -(8#64) from by decide]
  exact (BitVec.sub_eq_add_neg sp _).symm

/-- Execute all three temporary-frame stores and the actual raising-helper call. -/
theorem division_zero_setup {code sp env domain : BitVec 64} {c : Config}
    (h : DivisionZeroSetupInput code sp env domain c) :
    FnSummary 0x80003c90#64 (fun start => start = c) (DivisionZeroSetupPost code sp env domain c) := by
  constructor
  intro start initial
  obtain ⟨pc, eq⟩ := initial
  subst start
  obtain ⟨m1, m1Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 c.σ.mem sp.toNat (sdData_val (code + 8#64)) := ⟨_, rfl⟩
  obtain ⟨m2, m2Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 (divisionZeroEnvSp sp).toNat (sdData_val env) := ⟨_, rfl⟩
  obtain ⟨m3, m3Eq⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m2 (divisionZeroExtern domain).toNat (sdData_val (divisionZeroEnvSp sp)) := ⟨_, rfl⟩
  have stackMemory : m2 = writeLog c.σ.mem (divisionZeroStackLog code sp env) := by rw [m2Eq, m1Eq]; rfl
  have memoryLog : m3 = writeLog c.σ.mem (divisionZeroSetupLog code sp env domain) := by rw [m3Eq, stackMemory]; rfl
  have loaded : sign_extend (m := 64) (bytesT8 m2 Layout.sym_Caml_state) = domain :=
    (word_read_writeLog_out h.domainOutside stackMemory).trans h.domainWord
  have bp : SegSt 0x80003c90#64 [⟨Register.x8, code⟩, ⟨Register.x9, sp⟩, ⟨Register.x25, env⟩]
      (fun σ => Vsa.Sim.Code.CamlDivisionZeroSetupLoaded σ.mem ∧ σ.mem = c.σ.mem ∧ σ = c.σ) c :=
    ⟨h.good, pc, ⟨h.codeReg, h.stack, h.environment, trivial⟩, h.good.minstret, h.tick,
      division_zero_setup_loaded h.image, rfl, rfl⟩
  have native := tr_division_zero_setup code sp env c.σ.mem c.σ
  have globalAddress : (0x80003c9c#64 + sign_extend (m := 64) ((0x00061#20) +++ 0#12)) + sign_extend (m := 64) (0x06c#12) = BitVec.ofNat 64 Layout.sym_Caml_state := by decide
  simp only [globalAddress, show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from rfl, BitVec.add_zero,
    show sign_extend (m := 64) (0x008#12) = 8#64 from rfl, division_zero_env_sp,
    show sign_extend (m := 64) (0x0a0#12) = BitVec.ofNat 64 Layout.off_extern_sp from by decide] at native
  obtain ⟨count, after, _, run, post⟩ := native
    h.codeWrite.lower h.codeWrite.upper h.codeWrite.htif h.codeWrite.aligned
    (image_entry_code (w := code + 8#64) h.imageOutside (by simp [divisionZeroSetupLog, divisionZeroStackLog]) (by decide) (by decide)) m1 m1Eq
    h.envWrite.lower h.envWrite.upper h.envWrite.htif h.envWrite.aligned
    (image_entry_code (w := env) h.imageOutside (by simp [divisionZeroSetupLog, divisionZeroStackLog]) (by decide) (by decide)) m2 m2Eq
    (by decide) (by decide) (by decide) domain loaded.symm
    h.externWrite.lower h.externWrite.upper h.externWrite.htif h.externWrite.aligned
    (image_entry_code (w := divisionZeroEnvSp sp) h.imageOutside (by simp [divisionZeroSetupLog, divisionZeroExtern]) (by decide) (by decide)) m3 m3Eq c bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have writes := memory.trans memoryLog
  exact ⟨after, run.toSteps, post.good, image_of_writeLog h.image h.imageOutside writes,
    post.tick, post.pcAt, PinsHold.get post.pins ⟨0, by simp⟩, PinsHold.get post.pins ⟨1, by simp⟩,
    writes, frame.widenChecked (by decide)⟩

end OCaml.Vm.Sim
