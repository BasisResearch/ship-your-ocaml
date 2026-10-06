import OCaml.Vm.Sim.OperandStackRows
import OCaml.Vm.Sim.GlobalRows
import OCaml.Vm.Sim.ApplyGenericRows
import OCaml.Vm.Sim.ReturnRows
import OCaml.Vm.Sim.ControlRows
import OCaml.Bytecode.ExtraBound

/-!
# F1 table rows for the operand-taking stack, environment, global and call opcodes

Each row instantiates a loop-head simulation through `opArm_of_next1/2`.
Stack bounds come from the budget (`stack_fits`, `stack_fits_threshold`);
RETURN's saved-extra facts come from `ExtraBounded` (a2-sem).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Mis-shaped single-operand lists do not step. -/
theorem shape1 {P : Prog} {op : Opcode} (step : ∀ s, stepI P s ⟨op, []⟩ = .unsupported)
    (more : ∀ s a b rest, stepI P s ⟨op, a :: b :: rest⟩ = .unsupported) :
    ∀ s args, (∀ a, args ≠ [a]) →
      stepI P s ⟨op, args⟩ = .wrong ∨ stepI P s ⟨op, args⟩ = .unsupported := by
  intro s args ne
  rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact Or.inr (step s)
  · exact absurd rfl (ne a)
  · exact Or.inr (more s a b rest)

/-- Mis-shaped two-operand lists do not step. -/
theorem shape2 {P : Prog} {op : Opcode} (step : ∀ s, stepI P s ⟨op, []⟩ = .unsupported)
    (one : ∀ s a, stepI P s ⟨op, [a]⟩ = .unsupported)
    (more : ∀ s a b c rest, stepI P s ⟨op, a :: b :: c :: rest⟩ = .unsupported) :
    ∀ s args, (∀ a b, args ≠ [a, b]) →
      stepI P s ⟨op, args⟩ = .wrong ∨ stepI P s ⟨op, args⟩ = .unsupported := by
  intro s args ne
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact Or.inr (step s)
  · exact Or.inr (one s a)
  · exact absurd rfl (ne a b)
  · exact Or.inr (more s a b c rest)

/-- Unfold a step and close every halting branch. -/
macro "no_halt" step:ident : tactic => `(tactic| (
  simp only [stepI, opt] at $step:ident
  repeat' split at $step:ident
  all_goals first
    | exact enter_not_halt $step:ident
    | cases $step:ident))

/-- **The ACC n row.** -/
theorem acc_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog}
    (stable : MemoryStable L.runtimeOk) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .ACC :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      acc_next stable h code fetch (by simpa using stack_fits fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The PUSHACC n row.** -/
theorem pushacc_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHACC :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      pushacc_next rf h code fetch (stack_fits fits capacity reach) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The POP n row.** -/
theorem pop_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .POP :=
  opArm_of_next1 (fun _ _ _ _ _ _ h code fetch step => pop_next stable h code fetch step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The ASSIGN n row.** -/
theorem assign_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .ASSIGN :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      assign_next rf h code fetch (by simpa using stack_fits fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The ENVACC n row.** -/
theorem envacc_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .ENVACC :=
  opArm_of_next1 (fun _ _ _ _ _ _ h code fetch step => envacc_next stable h code fetch step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The GETGLOBAL n row.** -/
theorem getglobal_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .GETGLOBAL :=
  opArm_of_next1 (fun _ _ _ _ _ _ h code fetch step => getglobal_next stable h code fetch step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The PUSHGETGLOBAL n row.** -/
theorem pushgetglobal_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHGETGLOBAL :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      pushgetglobal_next rf h code fetch (stack_fits fits capacity reach) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The GETGLOBALFIELD n m row.** -/
theorem getglobalfield_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .GETGLOBALFIELD :=
  opArm_of_next2 (fun _ _ _ _ _ _ _ h code fetchN fetchM step =>
      getglobalfield_next stable h code fetchN fetchM step)
    (shape2 (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
    (fun s a b e w step => by no_halt step)

/-- **The PUSHGETGLOBALFIELD n m row.** -/
theorem pushgetglobalfield_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHGETGLOBALFIELD :=
  opArm_of_next2 (fun _ _ _ _ _ reach _ h code fetchN fetchM step =>
      pushgetglobalfield_next rf h code fetchN fetchM (stack_fits fits capacity reach) step)
    (shape2 (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
    (fun s a b e w step => by no_halt step)

/-- **The APPLY n row.** -/
theorem apply_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (stable : MemoryStable L.runtimeOk) (rf : RuntimeFrame L high0 dom0)
    (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPLY :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      apply_generic_next stable rf h code fetch
        (by simpa using stack_fits_threshold fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The APPTERM n s row.** -/
theorem appterm_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPTERM :=
  opArm_of_next2 (fun _ _ _ _ _ reach _ h code fetchN fetchS step =>
      appterm_generic_next rf h code fetchN fetchS
        (by simpa using stack_fits_threshold fits capacity reach (k := 0)) step)
    (shape2 (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl))
    (fun s a b e w step => by no_halt step)

/-- **The APPTERM1 s row.** -/
theorem appterm1_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPTERM1 :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      appterm1_next rf h code fetch
        (by simpa using stack_fits_threshold fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The APPTERM2 s row.** -/
theorem appterm2_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPTERM2 :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      appterm2_next rf h code fetch
        (by simpa using stack_fits_threshold fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The APPTERM3 s row.** -/
theorem appterm3_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPTERM3 :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      appterm3_next rf h code fetch
        (by simpa using stack_fits_threshold fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

/-- **The RETURN n row**, under a2-sem's `ExtraBounded`. -/
theorem return_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog}
    (stable : MemoryStable L.runtimeOk) (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (extra : ExtraBounded P) :
    OCaml.OpArm P (OCaml.LoopAt L P) .RETURN :=
  opArm_of_next1 (fun s _ _ w reach _ h code fetch step =>
      return_next stable h code fetch
        (by have := extra.small s reach; omega)
        (fun dest env ex rest frame => extra.saved s _ dest env ex rest reach frame)
        (by simpa using stack_fits fits capacity reach (k := 0)) step)
    (shape1 (fun _ => rfl) (fun _ _ _ _ => rfl)) (fun s a e w step => by no_halt step)

end OCaml.Vm.Sim
