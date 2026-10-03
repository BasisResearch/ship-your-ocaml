import OCaml.Vm.Sim.RetaddrStore
import OCaml.Vm.Sim.BranchArithmetic
import OCaml.Vm.Sim.PushRetaddrSegment
import OCaml.Vm.Sim.PushRetaddrPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- PUSH_RETADDR stores its represented code/environment/extra-argument frame
through the generated three-store body and shared stack-prefix restoration. -/
theorem push_retaddr_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {ofs : BitVec 32} {env : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 24, sp⟩])
    (h : ArmInput L P s .PUSH_RETADDR c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (jump : target s.pc 0 ofs.toInt = some dest)
    (envWord : valWord pl s.env = some env)
    (space : RetaddrWriteOk P s c pl cp sp dest env) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := s.pc + 2, stack := .code dest :: s.env :: Val.ofInt s.extra :: s.stack} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have envReg := represented_register h.env envWord
  obtain ⟨accu, accuReg, accuWord⟩ := h.accu
  have room16 : 16 ≤ sp := by have := space.room; omega
  have room8 : 8 ≤ sp := by have := space.room; omega
  have sp16 : (BitVec.ofNat 64 (sp - 16)).toNat = sp - 16 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have sp24 : (BitVec.ofNat 64 (sp - 24)).toNat = sp - 24 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have sp8 : (BitVec.ofNat 64 (sp - 8)).toNat = sp - 8 := Nat.mod_eq_of_lt (by have := space.stackNat; omega)
  have addr16 : BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12) = BitVec.ofNat 64 (sp - 16) :=
    stack_decrement room16 (by decide) (by decide)
  have addr24 : BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfe8#12) = BitVec.ofNat 64 (sp - 24) :=
    stack_decrement space.room (by decide) (by decide)
  have returnPC : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) +
      (BitVec.ofInt 64 ofs.toInt <<< (2 : Nat)) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    rw [codePc_succ]
    simpa only [Nat.add_zero] using relative_code_word pl jump
  have extraWord : Sail.shift_bits_left (BitVec.ofNat 64 s.extra) (Sail.BitVec.extractLsb (0x01#6) 5 0) +
      sign_extend (m := 64) (0x001#12) = tag64 (BitVec.ofNat 63 s.extra) := retaddr_extra_word s.extra
  obtain ⟨m1, hm1⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (sp - 16) (sdData_val env) := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 (sp - 24) (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * dest))) := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m2 (sp - 8) (sdData_val (tag64 (BitVec.ofNat 63 s.extra))) := ⟨_, rfl⟩
  have written : m3 = writeLog d.σ.mem (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
      (tag64 (BitVec.ofNat 63 s.extra))) := by rw [hm3, hm2, hm1]; rfl
  have code (a : Nat) (w : BitVec 64)
      (member : (a, 8, w) ∈ retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
        (tag64 (BitVec.ofNat 63 s.extra))) :
      a + 8 ≤ 0x80002c1c ∨ 0x80002c48 ≤ a := image_entry_code space.image member (by decide) (by decide)
  have envStore := writeWindow_nat space.envWindow sp16
  have pcStore := writeWindow_nat space.pcWindow sp24
  have extraStore := writeWindow_nat space.extraWindow sp8
  have bp : SegSt (0x80002c1c#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x18, BitVec.ofNat 64 s.extra⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x25, env⟩]
      (fun σ => Vsa.Sim.Code.CamlPushRetaddrLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
       (dp.frame.frame Register.x18 (by decide)).trans h.extra, dp.nextCode,
       (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
       (dp.frame.frame Register.x25 (by decide)).trans envReg, trivial⟩,
      dp.good.minstret, dp.tick, push_retaddr_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have read := operand.read32 h.code dp.memory
  have run := tr_push_retaddr (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 s.extra)
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) (BitVec.ofNat 64 sp) env d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, read, addr16, addr24, push_address room8,
    sp16, sp24, sp8, extraWord] at run
  have returnPC' : BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) +
      Sail.shift_bits_left (sign_extend (m := 64) ofs) (Sail.BitVec.extractLsb (0x02#6) 5 0) =
        BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    change BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) +
      (BitVec.ofInt 64 ofs.toInt <<< (2 : Nat)) = _
    simpa only [codePc_succ] using returnPC
  simp only [returnPC'] at run
  obtain ⟨nb, after, _, steps, post⟩ := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    envStore.lower envStore.upper envStore.htif envStore.aligned (code _ env (by simp [retaddrLog])) m1 hm1
    pcStore.lower pcStore.upper pcStore.htif pcStore.aligned (code _ (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (by simp [retaddrLog])) m2 hm2
    extraStore.lower extraStore.upper extraStore.htif extraStore.aligned (code _ (tag64 (BitVec.ofNat 63 s.extra)) (by simp [retaddrLog])) m3 hm3 d
    (by simpa only [codePc_succ] using bp)
  obtain ⟨_, memory, frame⟩ := post.extra
  have observed : StackPost d pl (s.pc + 2) (sp - 24) accu
      (writeLog d.σ.mem (retaddrLog sp (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) env
        (tag64 (BitVec.ofNat 63 s.extra)))) after := by
    refine ⟨post.good, post.pcAt, ?_, PinsHold.get post.pins ⟨0, by simp⟩,
      (frame.frame Register.x21 (by decide)).trans ((dp.frame.frame Register.x21 (by decide)).trans accuReg),
      memory.trans written, frame.out, fun r hr => frame.frame r (by revert r; decide)⟩
    have pc : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + sign_extend (m := 64) (0x008#12)) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (4 * 2) from by decide,
      codePc_add] using pc
  refine ⟨nb, after, steps, ?_⟩
  apply retaddr_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space envWord accuWord
  simpa only [dp.memory] using observed.after_dispatch dp

/-- Match the actual PUSH_RETADDR bytecode transition to the represented frame. -/
theorem push_retaddr_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {ofs : BitVec 32} {env : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 24, sp⟩])
    (h : ArmInput L P s .PUSH_RETADDR c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (jump : target s.pc 0 ofs.toInt = some dest)
    (envWord : valWord pl s.env = some env)
    (space : RetaddrWriteOk P s c pl cp sp dest env)
    (step : stepI P s ⟨.PUSH_RETADDR, [ofs.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 2, stack := .code dest :: s.env :: Val.ofInt s.extra :: s.stack} = s' := by
    simpa [stepI, jump, opt, St.adv] using step
  rw [← state]
  exact push_retaddr_arm stable h operand jump envWord space

end OCaml.Vm.Sim
