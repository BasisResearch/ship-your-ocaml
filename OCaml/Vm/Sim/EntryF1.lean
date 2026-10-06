import OCaml.Vm.Sim.EntryLoop
import OCaml.Vm.Gc.F1Runtime

/-!
# `ArmSim.entry` for the pinned F1 layout

Entry writes the interpreter's native frame (above the arena),
`caml_callback_depth` (carved out of the runtime footprint) and
`Caml_state->external_raise` (between the trap barrier and the backtrace
flag). None of them meets `Gc.f1Footprint`, so the pinned runtime invariant
survives entry (`f1_entryStable`), and `f1_entry` runs entry from `Loaded`.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The pinned runtime ignores entry's three write windows. -/
theorem f1_entryStable {sp : Nat} (frame : EntryFrame sp) :
    WindowStable Gc.f1Runtime (entryWindows sp Gc.f1Domain) := by
  obtain ⟨b1, b2, b3⟩ := frame.nat
  refine Gc.f1_stable ?_ ?_
  · intro w hw
    simp only [entryWindows, footprintWindows, entryFootprint, List.map, List.mem_cons, List.mem_nil_iff,
      or_false] at hw
    rcases hw with rfl | rfl | rfl
    rotate_left
    · exact Gc.footprint_apart_ignored ⟨⟨Layout.sym_caml_callback_depth, Layout.sym_caml_callback_depth + 4⟩,
        by simp [Gc.ignoredStatics], Nat.le_refl _, Nat.le_refl _⟩
    all_goals
      refine Gc.footprint_apart (Or.inl ?_) ?_
      · simp only [Gc.f1Domain, Boot.WhileMinRuntime.domain, Layout.sym_bss_end, Layout.off_external_raise,
          interpFrame, Layout.interpFrameBytes] at *; omega
      intro v hv
      simp only [Gc.youngWord, Gc.dynamicKept, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Gc.Apart, Gc.f1Domain, Boot.WhileMinRuntime.domain, Boot.WhileMinRuntime.freeBlock,
        Layout.sym_bss_end, Layout.off_young_ptr, Layout.off_stack_high,
        Layout.off_stack_threshold, Layout.off_trap_barrier, Layout.off_backtrace_active,
        Layout.off_external_raise, interpFrame, Layout.interpFrameBytes] <;> omega
  · intro w hw
    simp only [entryWindows, footprintWindows, entryFootprint, List.map, List.mem_cons, List.mem_nil_iff,
      or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Gc.heapSafe_native (by
        simp only [interpFrame, Layout.interpFrameBytes, Vsa.Sim.DlHeap.heapEnd] at *; omega)
    · exact Gc.mutable_heapSafe _ (by simp [Gc.mutableStatics])
    · exact Gc.heapSafe_domain (Nat.le_add_right _ _)
        (by simp only [Layout.off_external_raise, Layout.domainStateBytes]; omega)
        (Gc.TableFree.above (by simp only [Layout.off_external_raise, Layout.off_ref_table]; omega))

/-- **`ArmSim.entry` for the pinned F1 layout.** -/
theorem f1_entry {P : Prog} {c : Config} (h : OCaml.Loaded Gc.f1Layout P c) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt Gc.f1Layout P P.init c' := by
  obtain ⟨pl, cp, high, h⟩ := h
  obtain ⟨sp, regs, saved, caller⟩ := h.caller
  have dom : (word c Layout.sym_Caml_state).toNat = Gc.f1Domain := by
    have d := h.platform.runtime.freeListShape.domain
    rw [d, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simp only [Gc.f1Domain, Boot.WhileMinRuntime.domain]; omega)
  exact entry_loopAt h caller h.geometry (by rw [dom]; exact f1_entryStable (EntryFrame.of_caller caller))

end OCaml.Vm.Sim
