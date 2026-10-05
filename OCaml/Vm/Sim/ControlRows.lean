import OCaml.Vm.Sim.TrapRows
import OCaml.Vm.Sim.RestartRows
import OCaml.Vm.Sim.RetaddrRows
import OCaml.Vm.Sim.OffsetRows
import OCaml.Vm.Sim.DecodeFetch
import OCaml.Vm.Sim.ApplyRows

/-!
# F1 table rows for the control-transfer and trap families

Each row instantiates a loop-head simulation through `opArm_of_next0/1/2`;
stack bounds come from the budget (`stack_fits`, `stack_fits_threshold`) at
the state or its reachable successor.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem enter_not_halt {s : St} {stack : List Val} {extra e : Nat} {w : World} :
    enter s stack extra ≠ .halt e w := by
  intro h
  unfold enter at h
  cases hf : field? s.heap s.accu 0 with
  | none => rw [hf] at h; cases h
  | some v => rw [hf] at h; cases v <;> cases h

/-- **The POPTRAP row.** -/
theorem poptrap_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .POPTRAP :=
  opArm_of_next0 (fun _ _ _ reach _ h code step =>
      poptrap_next rf h code (by simpa using stack_fits fits capacity reach (k := 0)) step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by
      simp only [stepI] at step
      split at step
      · split at step <;> cases step
      · cases step)

/-- **The RESTART row.** -/
theorem restart_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .RESTART :=
  opArm_of_next0 (fun _ _ _ _ reach' h code step =>
      restart_next rf h code (by simpa using stack_fits fits capacity reach' (k := 0)) step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by
      simp only [stepI] at step
      split at step
      · split at step
        · split at step <;> cases step
        · cases step
      · cases step)

/-- **The PUSHTRAP row**, under the BcSem invariant that the trap pointer
never exceeds the stack (a2-sem). -/
theorem pushtrap_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B)
    (trapBounded : ∀ s, Reach P s → s.trap ≤ s.stack.length) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHTRAP :=
  opArm_of_next1 (fun s _ _ _ reach _ h code fetch step =>
      pushtrap_next rf h code fetch (by have := trapBounded s reach; omega)
        (stack_fits fits capacity reach) step)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact Or.inr rfl
      · exact absurd rfl (ne a)
      · exact Or.inr rfl)
    (fun s a e w => opt_not_halt)

/-- **The PUSH_RETADDR row.** -/
theorem push_retaddr_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSH_RETADDR :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      push_retaddr_next rf h code fetch (stack_fits fits capacity reach) step)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact Or.inr rfl
      · exact absurd rfl (ne a)
      · exact Or.inr rfl)
    (fun s a e w => opt_not_halt)

/-- **The APPLY1 row.** -/
theorem apply1_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPLY1 :=
  opArm_of_next0 (fun _ _ _ reach _ h code step =>
      apply1_next rf h code (stack_fits_threshold fits capacity reach) step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by
      simp only [stepI] at step
      split at step
      · exact enter_not_halt step
      · cases step)

/-- **The APPLY2 row.** -/
theorem apply2_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPLY2 :=
  opArm_of_next0 (fun _ _ _ reach _ h code step =>
      apply2_next rf h code (stack_fits_threshold fits capacity reach) step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by
      simp only [stepI] at step
      split at step
      · exact enter_not_halt step
      · cases step)

/-- **The APPLY3 row.** -/
theorem apply3_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .APPLY3 :=
  opArm_of_next0 (fun _ _ _ reach _ h code step =>
      apply3_next rf h code (stack_fits_threshold fits capacity reach) step)
    (fun s args ne => by cases args with | nil => exact absurd rfl ne | cons => exact Or.inr rfl)
    (fun s e w step => by
      simp only [stepI] at step
      split at step
      · exact enter_not_halt step
      · cases step)

/-- **The OFFSETCLOSURE n row.** -/
theorem offsetclosure_row {L : OCaml.Layout} {P : Prog} (stable : MemoryStable L.runtimeOk) :
    OCaml.OpArm P (OCaml.LoopAt L P) .OFFSETCLOSURE :=
  opArm_of_next1 (fun _ _ _ _ _ _ h code fetch step => offsetclosure_next stable h code fetch step)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact Or.inr rfl
      · exact absurd rfl (ne a)
      · exact Or.inr rfl)
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · split at step <;> cases step
      · cases step)

/-- **The PUSHOFFSETCLOSURE n row.** -/
theorem pushoffsetclosure_row {L : OCaml.Layout} {B : OCaml.Budget} {P : Prog} {high0 dom0 : Nat}
    (rf : RuntimeFrame L high0 dom0) (fits : OCaml.Fits B P) (capacity : StackCapacity B) :
    OCaml.OpArm P (OCaml.LoopAt L P) .PUSHOFFSETCLOSURE :=
  opArm_of_next1 (fun _ _ _ _ reach _ h code fetch step =>
      pushoffsetclosure_next rf h code fetch (stack_fits fits capacity reach) step)
    (fun s args ne => by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · exact Or.inr rfl
      · exact absurd rfl (ne a)
      · exact Or.inr rfl)
    (fun s a e w step => by
      simp only [stepI] at step
      split at step
      · split at step <;> cases step
      · cases step)

end OCaml.Vm.Sim
