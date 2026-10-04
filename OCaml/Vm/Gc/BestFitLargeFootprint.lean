import OCaml.Vm.Gc.BestFitLargeComplete

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- Split stores stay above the shared code/HTIF boundary. -/
theorem BestFitSplit.effect_high {request source c}
    (window : WriteWindow (BestFitSplit.headerAddr source) 8) :
    ∀ e ∈ BestFitSplit.effect request source c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  simp only [BestFitSplit.effect,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · change Layout.sym_tohost + 16 ≤ Layout.sym_caml_fl_cur_wsz
    decide
  · exact window.htif

theorem BestFitLarge.effect_high {sp c} (conditions : BestFitLarge.Conditions sp c) :
    ∀ e ∈ BestFitLarge.effect sp (BestFitLarge.size sp c) (BestFitLarge.header c),
      Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  simp only [BestFitLarge.effect,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact conditions.stack.size.htif
  · exact conditions.stack.bitmap.htif

theorem BestFitLarge.splitEffect_high {sp c} (conditions : BestFitLarge.Conditions sp c) :
    ∀ e ∈ BestFitLarge.splitEffect sp c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [BestFitLarge.splitEffect,List.mem_append] at member
  rcases member with member | member
  · exact BestFitLarge.effect_high conditions e member
  · exact BestFitSplit.effect_high conditions.headerWrite e member

theorem BestFitFallback.largeEffect_high {R c} (input : BestFitFallback.StackConditions R)
    (conditions : BestFitFallback.LargeConditions R c) :
    ∀ e ∈ BestFitFallback.largeEffect R c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [BestFitFallback.largeEffect,List.mem_append] at member
  rcases member with member | member
  · exact input.effect_high e member
  · exact BestFitLarge.splitEffect_high conditions.large e member

/-- Complete large-block allocation preserves any code image below HTIF. -/
theorem BestFitFallback.completeEffect_high {R c} (input : BestFitFallback.StackConditions R)
    (conditions : BestFitFallback.LargeConditions R c) :
    ∀ e ∈ BestFitFallback.completeEffect R c, Layout.sym_tohost + 16 ≤ e.1 := by
  intro e member
  rw [BestFitFallback.completeEffect,List.mem_append] at member
  rcases member with member | member
  · exact BestFitFallback.largeEffect_high input conditions e member
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    subst e
    change Layout.sym_tohost + 16 ≤ Layout.sym_caml_fl_cur_wsz
    decide

end OCaml.Vm.Gc
