import OCaml.Vm.Sim.RootFrame
import OCaml.Vm.Sim.FieldRead
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.ApplyArithmetic
import OCaml.Vm.Sim.EnterReady
import OCaml.Vm.Sim.ApplySegment
import OCaml.Vm.Sim.ApplyPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- APPLY enters the represented closure through the generated shared tail
when the runtime stack-capacity and no-pending checks succeed. -/
theorem apply_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {arity : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .APPLY c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) arity) (positive : 0 < arity.toInt)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8) (ready : EnterReady c sp) :
    ∃ after, Plus c after ∧ Running L P
      {s with pc := dest, env := s.accu, extra := arity.toInt.toNat - 1} after := by
  have source := represented_register h.accu field.sourceWord
  have fieldWord : word c (a + 8 * k) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
    (Option.some.inj (field.read h.toVmReprAt (by simp [roots])).word).symm
  have spNat : (BitVec.ofNat 64 sp).toNat = sp := by
    have shape := h.stack.1
    have highBound : high < 2^64 := by rw [← h.stackHigh]; exact BitVec.isLt _
    exact Nat.mod_eq_of_lt (by omega)
  have thresholdAddress : word c Layout.sym_Caml_state + sign_extend (m := 64) (0x098#12) =
      BitVec.ofNat 64 ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat]; rfl
  have capacity : zopz0zI_u (BitVec.ofNat 64 sp)
      (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)) = false := by
    apply bltu_false_of_ge
    rw [spNat]
    exact ready.capacity
  apply dispatch_compose h.dispatch
  intro d dp
  have read := operand.read32 h.code dp.memory
  have closureRead : sign_extend (m := 64) (bytesT8 d.σ.mem (a + 8 * k)) =
      BitVec.ofNat 64 (pl.codeBase + 4 * dest) :=
    (word_read_writeLog_out (log := []) trivial dp.memory).trans fieldWord
  have domainRead : sign_extend (m := 64) (bytesT8 d.σ.mem Layout.sym_Caml_state) = word c Layout.sym_Caml_state :=
    word_read_writeLog_out (log := []) trivial dp.memory
  have thresholdRead : sign_extend (m := 64)
      (bytesT8 d.σ.mem ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)) =
      word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold) :=
    word_read_writeLog_out (log := []) trivial dp.memory
  have bp : SegSt (0x80002bc0#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x21, BitVec.ofNat 64 (a + 8 * k)⟩,
       ⟨Register.x19, BitVec.ofNat 64 Layout.sym_Caml_state⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩,
       ⟨Register.x20, BitVec.ofNat 64 Layout.sym_caml_something_to_do⟩]
      (fun σ => Vsa.Sim.Code.CamlApplyLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x21 (by decide)).trans source,
      (dp.frame.frame Register.x19 (by decide)).trans h.dispatch.loop.domain,
      (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
      (dp.frame.frame Register.x20 (by decide)).trans h.dispatch.loop.pending, trivial⟩,
      dp.good.minstret, dp.tick, apply_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_apply (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 (a + 8 * k))
    (BitVec.ofNat 64 Layout.sym_Caml_state) (BitVec.ofNat 64 sp)
    (BitVec.ofNat 64 Layout.sym_caml_something_to_do) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, codePc_succ, operand.geometry.toNat, read, geometry.toNat,
    show (BitVec.ofNat 64 Layout.sym_Caml_state).toNat = Layout.sym_Caml_state from by decide,
    show (BitVec.ofNat 64 Layout.sym_caml_something_to_do).toNat = Layout.sym_caml_something_to_do from by decide] at run
  have run1 := run operand.geometry.lower operand.geometry.upper operand.geometry.htif (sign_extend (m := 64) arity) rfl
    geometry.lower geometry.upper geometry.htif (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) closureRead.symm
    (by decide) (by decide) (by decide) (word c Layout.sym_Caml_state) domainRead.symm
  simp only [thresholdAddress, ready.threshold.toNat] at run1
  obtain ⟨nb, after, _, steps, post⟩ := run1 ready.threshold.lower ready.threshold.upper ready.threshold.htif
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)) thresholdRead.symm capacity
    (by decide) (by decide) (by decide) 0#64 (ready.toSignalCheckReady.read dp.memory).symm (by decide) d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  have payload := payload_pc (payload_extra
    (payload_env_of_root (payload_of_repr h.toVmReprAt) s.accu
      (fun _ loc => Live.root (by simp [roots]) loc)) (arity.toInt.toNat - 1)) dest
  have regs : VmRegisters {s with pc := dest, env := s.accu, extra := arity.toInt.toNat - 1} pl sp after := by
    refine ⟨post.pcAt, PinsHold.get post.pins ⟨4, by simp⟩,
      PinsHold.get post.pins ⟨7, by simp⟩,
      ⟨_, PinsHold.get post.pins ⟨5, by simp⟩, field.sourceWord⟩,
      ⟨_, PinsHold.get post.pins ⟨2, by simp⟩, field.sourceWord⟩, ?_⟩
    have extra : gpr after Layout.reg_extra = some
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (sign_extend (m := 64) arity + sign_extend (m := 64) (0xfff#12)) 31 0)) :=
      PinsHold.get post.pins ⟨3, by simp⟩
    simpa only [apply_count_word arity positive] using extra
  refine ⟨nb, after, steps, ?_⟩
  apply readOnly_restore stable payload h.primitives h.running.platform regs
    (loopRegisters_frame (fun r hr => (frame.frame r (by revert r; decide)).trans
      (dp.frame.frame r (by revert r; decide))) h.dispatch.loop)
    post.good (memory.trans dp.memory) (frame.out.trans dp.frame.out)
    (h.geometry.state rfl rfl) h.native
    ((frame.frame (gprReg 2) (by decide)).trans (dp.frame.frame (gprReg 2) (by decide)))

/-- Successful APPLY supplies a positive arity; closure entry agrees with
its represented field and the generated no-growth/no-pending path. -/
theorem apply_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a k dest : Nat} {arity : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .APPLY c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) arity)
    (field : FieldSelection s.heap pl s.accu 0 (.code dest) l a k)
    (geometry : RamReadAt (a + 8 * k) 8) (ready : EnterReady c sp)
    (step : stepI P s ⟨.APPLY, [arity.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have positive : 0 < arity.toInt := by
    by_cases positive : 0 < arity.toInt
    · exact positive
    · have bad : arity.toInt < 1 := by omega
      simp only [stepI, bad, ite_true] at step
      cases step
  have state : {s with pc := dest, env := s.accu, extra := arity.toInt.toNat - 1} = s' := by
    simpa only [stepI, show ¬ arity.toInt < 1 by omega, ite_false, enter, field.selected,
      opt, Res.next.injEq] using step
  rw [← state]
  exact apply_arm stable h operand positive field geometry ready

end OCaml.Vm.Sim
