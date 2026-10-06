import OCaml.Vm.Sim.ConsoleCall
import OCaml.Vm.Gc.F1Runtime
import OCaml.Refinement

/-!
# The console primitives keep the F1 runtime invariant

a1-prims' `ConsoleStable` (`ConsoleCall.lean`): the console primitives write
the native stack below the C-call `sp`, newlib's two `errno` words and the
channel record's `offset`, `curr` and buffer. The F1 runtime invariant
survives (`f1_console_stable`):
* the native window lies above the allocator arena (`heapSafe_native`), hence
  above the whole runtime footprint (`footprint_below_heapEnd`);
* the `errno` words are mutable statics;
* the record windows miss the record's `next` link, and the record is open:
  `NurseryGeometry.channelsListed` puts every placed channel on the runtime's
  open-channel list (`Gc.f1_records`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Every footprint window lies below the allocator arena's end. -/
theorem footprint_below_heapEnd : ∀ v ∈ Gc.f1Footprint, v.hi ≤ Vsa.Sim.DlHeap.heapEnd := by
  intro v hv
  rcases List.mem_cons.1 hv with rfl | hv
  · simp only [Gc.youngWord, Gc.f1Domain, Boot.WhileMinRuntime.domain, Layout.off_young_ptr,
      Vsa.Sim.DlHeap.heapEnd]
    omega
  rcases List.mem_append.1 hv with hs | hd
  · have := Gc.staticKept_below v hs
    simp only [Layout.sym_bss_end, Vsa.Sim.DlHeap.heapEnd] at *
    omega
  · simp only [Gc.dynamicKept, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Gc.f1Domain, Boot.WhileMinRuntime.domain, Boot.WhileMinRuntime.freeBlock, Layout.off_young_ptr,
        Layout.off_stack_high, Layout.off_stack_threshold, Layout.off_trap_barrier, Layout.off_backtrace_active,
        Vsa.Sim.DlHeap.heapEnd] <;> omega

/-- A window above the arena misses the footprint and is safe for newlib's heap. -/
theorem native_safe {lo hi : Nat} (low : Vsa.Sim.DlHeap.heapEnd ≤ lo) :
    (∀ v ∈ Gc.f1Footprint, Gc.Apart ⟨lo, hi⟩ v) ∧ Gc.F1HeapSafe ⟨lo, hi⟩ :=
  ⟨fun v hv => Or.inr (Nat.le_trans (footprint_below_heapEnd v hv) low), Gc.heapSafe_native low⟩

/-- A mutable static misses the footprint and is safe for newlib's heap. -/
theorem mutable_safe {w : W} (hw : w ∈ Gc.mutableStatics) :
    (∀ v ∈ Gc.f1Footprint, Gc.Apart w v) ∧ Gc.F1HeapSafe w :=
  ⟨Gc.footprint_apart_ignored ⟨w, Gc.mutableStatics_ignored w hw, Nat.le_refl _, Nat.le_refl _⟩,
    Gc.mutable_heapSafe w hw⟩

theorem errno_mutable : (⟨Layout.sym_errno, Layout.sym_errno + 4⟩ : W) ∈ Gc.mutableStatics :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem impure_mutable : (⟨Layout.sym_impure_data, Layout.sym_impure_data + 4⟩ : W) ∈ Gc.mutableStatics :=
  List.mem_cons_self

/-- **`ConsoleStable` for the pinned F1 layout.** -/
theorem f1_console_stable : ConsoleStable Gc.f1Layout := by
  intro P s c pl cp high id chn a sp g ok hc hp low _ c' frame
  obtain ⟨chs, list, placed, -⟩ := g.nursery.channelsListed
  refine Gc.f1_records (a := a) ?_ ⟨chs, list, placed id chn a hc hp⟩ frame ok
  intro w hw
  have room : a + 72 + OCaml.Bytecode.ioBufferSize ≤ a + Gc.chanRecordBytes := by
    simp only [Gc.chanRecordBytes, chanOffBuff]; omega
  simp only [consoleWindows, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · have hn : Vsa.Sim.DlHeap.heapEnd + 384 ≤ sp :=
      Nat.le_trans (Nat.add_le_add_left (by decide : 384 ≤ nativeHeadroom) _) low
    exact Or.inl (native_safe (lo := sp - 384) (hi := sp) (Nat.le_sub_of_add_le hn))
  · exact Or.inl (mutable_safe errno_mutable)
  · exact Or.inl (mutable_safe impure_mutable)
  all_goals
    refine Or.inr ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
    dsimp only
    simp only [Gc.chanOffNext]
    omega

end OCaml.Vm.Sim
