import OCaml.Vm.Sim.Setglobal
import OCaml.Vm.Sim.Setfield
import OCaml.Vm.Sim.Setfield0
import OCaml.Vm.Sim.Setfield1
import OCaml.Vm.Sim.Setfield2
import OCaml.Vm.Sim.Setfield3
import OCaml.Vm.Sim.FieldOperandRows

/-!
# SETGLOBAL and SETFIELD from the loop head

The store goes through `caml_modify`. Its machine summary is the GC lane's
named obligation, stated per call site exactly as the arm consumes it
(`GlobalBarrier`, `FieldBarrier`, `FieldBarrierK`). Every other premise
(operand, represented values, the stacked value's read window) comes from
the loop head.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **caml_modify at SETGLOBAL** (named obligation, GC lane). -/
structure GlobalBarrier (L : OCaml.Layout) (P : Prog) : Prop where
  callee : ∀ s c pl cp sp high (ofs : BitVec 32) value heap, Reach P s →
    ArmInput L P s .SETGLOBAL c pl cp sp high → 0 ≤ ofs.toInt → valWord pl s.accu = some value →
    setField? s.heap P.globals ofs.toInt.toNat s.accu = some heap →
    ModifyCallee L P s {s with pc := s.pc + 2, accu := .unit, heap := heap, stack := s.stack} pl cp sp sp high 8
      (0x800025c8#64) (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp)
      (BitVec.ofNat 64 (8 * ofs.toInt.toNat) + word c Layout.sym_caml_global_data) value

/-- **caml_modify at SETFIELD n** (named obligation, GC lane). -/
structure FieldBarrier (L : OCaml.Layout) (P : Prog) : Prop where
  callee : ∀ s c pl cp sp high (ofs : BitVec 32) base value v rest heap, Reach P s →
    ArmInput L P s .SETFIELD c pl cp sp high → 0 ≤ ofs.toInt → valWord pl s.accu = some base →
    s.stack = v :: rest → valWord pl v = some value →
    setField? s.heap s.accu ofs.toInt.toNat v = some heap →
    ModifyCallee L P s {s with pc := s.pc + 2, accu := .unit, heap := heap, stack := rest} pl cp sp (sp + 8) high 8
      (0x8000214c#64) (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2))) (BitVec.ofNat 64 sp)
      (BitVec.ofNat 64 (8 * ofs.toInt.toNat) + base) value

/-- **caml_modify at SETFIELDk** (named obligation, GC lane): field `k`,
return site `ra`, slot offset `off = 8k`. -/
structure FieldBarrierK (L : OCaml.Layout) (P : Prog) (op : Opcode) (k : Nat) (ra off : BitVec 64) : Prop where
  callee : ∀ s c pl cp sp high base value v rest heap, Reach P s →
    ArmInput L P s op c pl cp sp high → valWord pl s.accu = some base →
    s.stack = v :: rest → valWord pl v = some value → setField? s.heap s.accu k v = some heap →
    ModifyCallee L P s {s with pc := s.pc + 1, accu := .unit, heap := heap, stack := rest} pl cp sp (sp + 8) high 23
      ra (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) (BitVec.ofNat 64 sp + 8#64) (base + off) value

/-- **The SETGLOBAL row.** -/
theorem setglobal_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (barrier : GlobalBarrier L P) : OCaml.OpArm P (OCaml.LoopAt L P) .SETGLOBAL :=
  opArm_of_next1 (fun s s' c w reach _ h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      have body := Res.unguard step
      change opt (setField? s.heap P.globals w.toInt.toNat s.accu)
        (fun hp => .next { (s.adv 2) with heap := hp, accu := .unit }) = .next s' at body
      obtain ⟨heap, update, -⟩ := opt_next body
      obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
      obtain ⟨value, -, encoded⟩ := input.accu
      obtain ⟨c', run, running⟩ := setglobal_step_arm stable input (OperandAt.of_fetch input.geometry fetch)
        nonnegative input.globals encoded
        (barrier.callee s c pl cp sp high w value heap reach input nonnegative encoded update) update step
      exact ⟨c', run, h.of_plus run running⟩)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The SETFIELD n row.** -/
theorem setfield_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B) (barrier : FieldBarrier L P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .SETFIELD :=
  opArm_of_next1 (fun s s' c w reach _ h code fetch step => by
      have nonnegative : 0 ≤ w.toInt := Int.not_lt.mp (Res.guard_ok step)
      have body := Res.unguard step
      cases hs : s.stack with
      | nil => simp [hs] at body
      | cons v rest =>
        simp only [hs] at body
        obtain ⟨heap, update, -⟩ := opt_next body
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨base, -, source⟩ := input.accu
        have encoded := input.stack.2 0 v (by simp [hs])
        have space := stack_space input.stack (by simpa using stack_fits fits capacity reach (k := 0))
        have read := input.geometry.read input.stack space (i := 0) (by simp [hs])
        simp only [Nat.mul_zero, Nat.add_zero] at encoded read
        obtain ⟨c', run, running⟩ := setfield_step_arm stable input (OperandAt.of_fetch input.geometry fetch)
          nonnegative source hs encoded read
          (barrier.callee s c pl cp sp high w base _ v rest heap reach input nonnegative source hs encoded update)
          update step
        exact ⟨c', run, h.of_plus run running⟩)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The SETFIELD0 row.** -/
theorem setfield0_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (barrier : FieldBarrierK L P .SETFIELD0 0 (0x800021bc#64) (0#64)) :
    OCaml.OpArm P (OCaml.LoopAt L P) .SETFIELD0 :=
  opArm_of_next0 (fun s s' c reach _ h code step => by
      have body := step
      cases hs : s.stack with
      | nil => simp [stepI, hs] at body
      | cons v rest =>
        simp only [stepI, hs] at body
        obtain ⟨heap, update, -⟩ := opt_next body
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨base, -, source⟩ := input.accu
        have encoded := input.stack.2 0 v (by simp [hs])
        have space := stack_space input.stack (by simpa using stack_fits fits capacity reach (k := 0))
        have read := (input.geometry.read input.stack space (i := 0) (by simp [hs])).window
        simp only [Nat.mul_zero, Nat.add_zero] at encoded read
        obtain ⟨c', run, running⟩ := setfield0_step_arm stable input source hs encoded read
          (barrier.callee s c pl cp sp high base _ v rest heap reach input source hs encoded update) update step
        exact ⟨c', run, h.of_plus run running⟩)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by no_halt step)

/-- **The SETFIELD1 row.** -/
theorem setfield1_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (barrier : FieldBarrierK L P .SETFIELD1 1 (0x800021a0#64) (8#64)) :
    OCaml.OpArm P (OCaml.LoopAt L P) .SETFIELD1 :=
  opArm_of_next0 (fun s s' c reach _ h code step => by
      have body := step
      cases hs : s.stack with
      | nil => simp [stepI, hs] at body
      | cons v rest =>
        simp only [stepI, hs] at body
        obtain ⟨heap, update, -⟩ := opt_next body
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨base, -, source⟩ := input.accu
        have encoded := input.stack.2 0 v (by simp [hs])
        have space := stack_space input.stack (by simpa using stack_fits fits capacity reach (k := 0))
        have read := (input.geometry.read input.stack space (i := 0) (by simp [hs])).window
        simp only [Nat.mul_zero, Nat.add_zero] at encoded read
        obtain ⟨c', run, running⟩ := setfield1_step_arm stable input source hs encoded read
          (barrier.callee s c pl cp sp high base _ v rest heap reach input source hs encoded update) update step
        exact ⟨c', run, h.of_plus run running⟩)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by no_halt step)

/-- **The SETFIELD2 row.** -/
theorem setfield2_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (barrier : FieldBarrierK L P .SETFIELD2 2 (0x80002184#64) (16#64)) :
    OCaml.OpArm P (OCaml.LoopAt L P) .SETFIELD2 :=
  opArm_of_next0 (fun s s' c reach _ h code step => by
      have body := step
      cases hs : s.stack with
      | nil => simp [stepI, hs] at body
      | cons v rest =>
        simp only [stepI, hs] at body
        obtain ⟨heap, update, -⟩ := opt_next body
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨base, -, source⟩ := input.accu
        have encoded := input.stack.2 0 v (by simp [hs])
        have space := stack_space input.stack (by simpa using stack_fits fits capacity reach (k := 0))
        have read := (input.geometry.read input.stack space (i := 0) (by simp [hs])).window
        simp only [Nat.mul_zero, Nat.add_zero] at encoded read
        obtain ⟨c', run, running⟩ := setfield2_step_arm stable input source hs encoded read
          (barrier.callee s c pl cp sp high base _ v rest heap reach input source hs encoded update) update step
        exact ⟨c', run, h.of_plus run running⟩)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by no_halt step)

/-- **The SETFIELD3 row.** -/
theorem setfield3_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} (stable : MemoryStable L.runtimeOk)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (barrier : FieldBarrierK L P .SETFIELD3 3 (0x80002168#64) (24#64)) :
    OCaml.OpArm P (OCaml.LoopAt L P) .SETFIELD3 :=
  opArm_of_next0 (fun s s' c reach _ h code step => by
      have body := step
      cases hs : s.stack with
      | nil => simp [stepI, hs] at body
      | cons v rest =>
        simp only [stepI, hs] at body
        obtain ⟨heap, update, -⟩ := opt_next body
        obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
        obtain ⟨base, -, source⟩ := input.accu
        have encoded := input.stack.2 0 v (by simp [hs])
        have space := stack_space input.stack (by simpa using stack_fits fits capacity reach (k := 0))
        have read := (input.geometry.read input.stack space (i := 0) (by simp [hs])).window
        simp only [Nat.mul_zero, Nat.add_zero] at encoded read
        obtain ⟨c', run, running⟩ := setfield3_step_arm stable input source hs encoded read
          (barrier.callee s c pl cp sp high base _ v rest heap reach input source hs encoded update) update step
        exact ⟨c', run, h.of_plus run running⟩)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by no_halt step)

end OCaml.Vm.Sim
