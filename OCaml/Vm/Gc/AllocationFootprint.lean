import OCaml.Vm.Gc.AllocWrapper

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

theorem AllocEntry.effect_high {R} (windows : AllocEntry.Windows R) :
    ∀ e ∈ AllocEntry.effect R, Layout.sym_tohost + 16 ≤ e.1 := by
  rw [AllocEntry.effect_bank]
  apply SaveBank.high
  intro cell member
  simp only [AllocEntry.saveCells,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | rfl
  · exact windows.saved cell member
  · exact windows.tag

/-- Both the free-list and wrapper-continuation stores respect the common
code-image boundary, independently of the register/platform obligations. -/
theorem AllocExact.effect_high {sp size c}
    (free : BestFitExact.Conditions size c)
    (continuation : AllocSuccess.Conditions (AllocExact.returnRegs sp size c) (AllocExact.allocated size c)) :
    ∀ e ∈ AllocExact.effect sp size c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [AllocExact.effect,List.mem_append] at member
  rcases member with member | member
  · exact free.effect_high e member
  · simp only [AllocAccount.effect,AllocAccount.headerLog,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact continuation.account.headerWrite.htif
    · change Layout.sym_tohost + 16 ≤ Layout.sym_caml_allocated_words
      decide

theorem AllocWrapper.effect_high {R c} (windows : AllocEntry.Windows R)
    (conditions : AllocWrapper.Conditions R c) :
    ∀ e ∈ AllocWrapper.effect R c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [AllocWrapper.effect,List.mem_append] at member
  rcases member with member | member
  · exact AllocEntry.effect_high windows e member
  · exact AllocExact.effect_high conditions.freeList conditions.continuation e member

end OCaml.Vm.Gc
