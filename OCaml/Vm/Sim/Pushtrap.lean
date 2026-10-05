import OCaml.Vm.Sim.PushtrapRestore
import OCaml.Vm.Sim.BranchArithmetic
import OCaml.Vm.Sim.PushtrapSegment
import OCaml.Vm.Sim.PushtrapPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- PUSHTRAP saves a represented handler frame and installs it as the current
trap through the generated body, including both intervening domain loads. -/
theorem pushtrap_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {ofs : BitVec 32} {env : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 32, sp⟩,
      ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
       (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (h : ArmInput L P s .PUSHTRAP c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (jump : target s.pc 0 ofs.toInt = some dest)
    (envWord : valWord pl s.env = some env)
    (space : PushtrapWriteOk P s c pl cp sp high dest env) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := s.pc + 2, stack := .code dest :: Val.ofInt (s.stack.length + 4 - s.trap : Nat) :: s.env :: Val.ofInt s.extra :: s.stack, trap := s.stack.length + 4} after := by
  have envReg := represented_register h.env envWord
  obtain ⟨accu, accuReg, accuWord⟩ := h.accu
  have shape := h.stack.1
  have room := space.room
  have small := space.highSmall
  have natAt (n : Nat) : (BitVec.ofNat 64 (sp - n)).toNat = sp - n := Nat.mod_eq_of_lt (by omega)
  have addr32 : BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfe0#12) = BitVec.ofNat 64 (sp - 32) :=
    stack_decrement room (by decide) (by decide)
  have addr24 : BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfe8#12) = BitVec.ofNat 64 (sp - 24) :=
    stack_decrement (by omega) (by decide) (by decide)
  have addr16 : BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12) = BitVec.ofNat 64 (sp - 16) :=
    stack_decrement (by omega) (by decide) (by decide)
  have addr8 := push_address (show 8 ≤ sp by omega)
  have domainAddress : ((0x80003180#64) + sign_extend (m := 64) ((0x00062#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xb88#12) = BitVec.ofNat 64 Layout.sym_Caml_state := by decide
  have trapAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x0a8#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have trapNat : (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)).toNat =
      (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp := Nat.mod_eq_of_lt space.domainAddress
  have trapWindow : WriteWindow (BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)) 8 := by
    rw [← trapAddress]; exact space.trapWindow
  have trapStore := writeWindow_nat trapWindow trapNat
  have trapReadHtif : (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8 ≤ tohostAddr ∨
      tohostAddr + 8 ≤ (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp :=
    Or.inr (by have htif := trapStore.htif; omega)
  have codeStore := writeWindow_nat space.codeWindow (natAt 32)
  have extraStore := writeWindow_nat space.extraWindow (natAt 8)
  have envStore := writeWindow_nat space.envWindow (natAt 16)
  have linkStore := writeWindow_nat space.linkWindow (natAt 24)
  have handler : BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) +
      Sail.shift_bits_left (sign_extend (m := 64) ofs) (Sail.BitVec.extractLsb (0x02#6) 5 0) =
        BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    change BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) + (BitVec.ofInt 64 ofs.toInt <<< (2 : Nat)) = _
    simpa only [Nat.add_zero] using relative_code_word pl jump
  have extraWord : Sail.shift_bits_left (BitVec.ofNat 64 s.extra) (Sail.BitVec.extractLsb (0x01#6) 5 0) +
      sign_extend (m := 64) (0x001#12) = tag64 (BitVec.ofNat 63 s.extra) := retaddr_extra_word s.extra
  have linkWord : Sail.shift_bits_left
      (shift_bits_right_arith (BitVec.ofNat 64 (high - 8 * s.trap) - BitVec.ofNat 64 (sp - 32))
        (Sail.BitVec.extractLsb (0x03#6) 5 0)) (Sail.BitVec.extractLsb (0x01#6) 5 0) +
      sign_extend (m := 64) (0x001#12) = tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)) :=
    pushtrap_link shape room small space.trapBound
  have oldTrap : word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) =
      BitVec.ofNat 64 (high - 8 * s.trap) := by
    rw [← h.trapsp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have code (a : Nat) (w : BitVec 64)
      (member : (a, 8, w) ∈ pushtrapLog sp (word c Layout.sym_Caml_state).toNat
        (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
        env (tag64 (BitVec.ofNat 63 s.extra))) : a + 8 ≤ 0x8000317c ∨ 0x800031d8 ≤ a :=
    image_entry_code space.image member (by decide) (by decide)
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨m1, hm1⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 d.σ.mem (sp - 32) (sdData_val (BitVec.ofNat 64 (pl.codeBase + 4 * dest))) := ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m1 (sp - 8) (sdData_val (tag64 (BitVec.ofNat 63 s.extra))) := ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m2 (sp - 16) (sdData_val env) := ⟨_, rfl⟩
  obtain ⟨m4, hm4⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m3 (sp - 24) (sdData_val (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))) := ⟨_, rfl⟩
  obtain ⟨m5, hm5⟩ : ∃ m : Std.ExtHashMap Nat (BitVec 8),
      m = writeMap8 m4 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)
        (sdData_val (BitVec.ofNat 64 (sp - 32))) := ⟨_, rfl⟩
  have written : m5 = writeLog d.σ.mem (pushtrapLog sp (word c Layout.sym_Caml_state).toNat
      (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
      env (tag64 (BitVec.ofNat 63 s.extra))) := by rw [hm5, hm4, hm3, hm2, hm1]; rfl
  have prefix1 : m1 = writeLog c.σ.mem [(sp - 32, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest))] := by
    rw [hm1, dp.memory]; rfl
  have prefix4 : m4 = writeLog c.σ.mem ((pushtrapLog sp (word c Layout.sym_Caml_state).toNat
      (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
      env (tag64 (BitVec.ofNat 63 s.extra))).take 4) := by rw [hm4, hm3, hm2, hm1, dp.memory]; rfl
  have domain1 : sign_extend (m := 64) (bytesT8 m1 Layout.sym_Caml_state) = word c Layout.sym_Caml_state :=
    word_read_writeLog_out (outLRange_sublist (List.take_sublist 1 _) space.payload.domain) prefix1
  have domain4 : sign_extend (m := 64) (bytesT8 m4 Layout.sym_Caml_state) = word c Layout.sym_Caml_state :=
    word_read_writeLog_out (outLRange_sublist (List.take_sublist 4 _) space.payload.domain) prefix4
  have trap1 : sign_extend (m := 64) (bytesT8 m1 ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp)) =
      BitVec.ofNat 64 (high - 8 * s.trap) := by
    rw [← oldTrap]
    apply word_read_writeLog_out (log := [(sp - 32, 8, BitVec.ofNat 64 (pl.codeBase + 4 * dest))]) _ prefix1
    have separate := space.separate
    simp only [OutLRange, and_true]
    omega
  have bp : SegSt (0x8000317c#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x9, BitVec.ofNat 64 sp⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩,
       ⟨Register.x18, BitVec.ofNat 64 s.extra⟩, ⟨Register.x25, env⟩]
      (fun σ => Vsa.Sim.Code.CamlPushtrapLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg, dp.nextCode,
      (dp.frame.frame Register.x18 (by decide)).trans h.extra,
      (dp.frame.frame Register.x25 (by decide)).trans envReg, trivial⟩,
      dp.good.minstret, dp.tick, pushtrap_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_pushtrap (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp)
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) (BitVec.ofNat 64 s.extra) env d.σ.mem d.σ
  have read := operand.read32 h.code dp.memory
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, codePc_succ, operand.geometry.toNat, read, addr32, addr24, addr16, addr8,
    natAt, domainAddress, show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide,
    extraWord] at run
  have run1 := run operand.geometry.lower operand.geometry.upper operand.geometry.htif (sign_extend (m := 64) ofs) rfl
  simp only [handler] at run1
  have run2 := run1 codeStore.lower codeStore.upper codeStore.htif codeStore.aligned
    (code _ (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (by simp [pushtrapLog])) m1 hm1
    (by decide) (by decide) (by decide) (word c Layout.sym_Caml_state) domain1.symm
  simp only [trapAddress, trapNat] at run2
  have run3 := run2 trapStore.lower trapStore.upper trapReadHtif (BitVec.ofNat 64 (high - 8 * s.trap)) trap1.symm
    extraStore.lower extraStore.upper extraStore.htif extraStore.aligned
    (code _ (tag64 (BitVec.ofNat 63 s.extra)) (by simp [pushtrapLog])) m2 hm2
    envStore.lower envStore.upper envStore.htif envStore.aligned (code _ env (by simp [pushtrapLog])) m3 hm3
  simp only [linkWord] at run3
  have run4 := run3 linkStore.lower linkStore.upper linkStore.htif linkStore.aligned
    (code _ (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap))) (by simp [pushtrapLog])) m4 hm4
    (by decide) (by decide) (by decide) (word c Layout.sym_Caml_state) domain4.symm
  simp only [trapAddress, trapNat] at run4
  obtain ⟨nb, after, _, steps, post⟩ := run4 trapStore.lower trapStore.upper trapStore.htif trapStore.aligned
    (code _ (BitVec.ofNat 64 (sp - 32)) (by simp [pushtrapLog])) m5 hm5 d
    (by simpa only [codePc_succ] using bp)
  obtain ⟨_, memory, frame⟩ := post.extra
  have observed : StackPost d pl (s.pc + 2) (sp - 32) accu
      (writeLog d.σ.mem (pushtrapLog sp (word c Layout.sym_Caml_state).toNat
        (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (tag64 (BitVec.ofNat 63 (s.stack.length + 4 - s.trap)))
        env (tag64 (BitVec.ofNat 63 s.extra)))) after := by
    refine ⟨post.good, post.pcAt, ?_, PinsHold.get post.pins ⟨0, by simp⟩,
      (frame.frame Register.x21 (by
        simp only [List.forall_mem_append, List.forall_mem_cons]
        decide)).trans ((dp.frame.frame Register.x21 (by
        simp only [List.forall_mem_append, List.forall_mem_cons]
        decide)).trans accuReg),
      memory.trans written, frame.out, fun r hr => frame.frame r (by
        simp only [List.forall_mem_append, List.forall_mem_cons]
        revert r; decide)⟩
    have pc : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + sign_extend (m := 64) (0x008#12)) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (4 * 2) from by decide, codePc_add] using pc
  refine ⟨nb, after, steps, ?_⟩
  apply pushtrap_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space envWord accuWord
  case geometry => exact h.geometry
  case native => exact h.native
  simpa only [dp.memory] using observed.after_dispatch dp

/-- Match the actual PUSHTRAP bytecode transition to its represented frame. -/
theorem pushtrap_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {ofs : BitVec 32} {env : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 32, sp⟩,
      ⟨(word c Layout.sym_Caml_state).toNat + Layout.off_trapsp,
       (word c Layout.sym_Caml_state).toNat + Layout.off_trapsp + 8⟩])
    (h : ArmInput L P s .PUSHTRAP c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) ofs)
    (jump : target s.pc 0 ofs.toInt = some dest)
    (envWord : valWord pl s.env = some env)
    (space : PushtrapWriteOk P s c pl cp sp high dest env)
    (step : stepI P s ⟨.PUSHTRAP, [ofs.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 2, stack := .code dest :: Val.ofInt (s.stack.length + 4 - s.trap : Nat) :: s.env :: Val.ofInt s.extra :: s.stack, trap := s.stack.length + 4} = s' := by
    simpa [stepI, jump, opt, St.adv, Int.ofNat_sub space.trapBound] using step
  rw [← state]
  exact pushtrap_arm stable h operand jump envWord space

end OCaml.Vm.Sim
