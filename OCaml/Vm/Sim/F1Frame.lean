import OCaml.Vm.Gc.F1Runtime
import OCaml.Vm.Sim.StackRows

/-!
# The F1 runtime layout discharges the arms' runtime contracts

a6-gc's pinned F1 layout (`Gc.f1Layout`, runtime invariant `Gc.f1Runtime`)
supplies `RuntimeFrame` (stack window, stack_high/threshold words, no pending
signal) and `MemoryStable`, the two runtime premises of the loop-head rows.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm

/-- Every VM window is apart from the F1 runtime footprint. -/
theorem f1_vmWindow_apart {w : W} (vm : VmWindow Gc.f1High Gc.f1Domain w) :
    ∀ v ∈ Gc.f1Footprint, Gc.Apart w v := by
  rcases vm with ⟨low, high⟩ | ⟨off, member, rfl⟩
  · exact Gc.stackWindow_apart low high
  · exact Gc.domainField_apart (by
      simp only [vmDomainOffsets, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with h | h | h | h <;> simp [h])

/-- Every VM window is safe for newlib's heap: it lies in the VM stack or the
`Caml_state` record, both runtime blocks. -/
theorem f1_vmWindow_heapSafe {w : W} (vm : VmWindow Gc.f1High Gc.f1Domain w) : Gc.F1HeapSafe w := by
  rcases vm with ⟨low, high⟩ | ⟨off, member, rfl⟩
  · exact Gc.heapSafe_stack low high
  · simp only [vmDomainOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    refine Gc.heapSafe_domain (Nat.le_add_right _ _) ?_ (Or.inr ?_) <;>
    rcases member with rfl | rfl | rfl | rfl <;>
      simp only [Layout.off_trapsp, Layout.off_extern_sp, Layout.off_local_roots, Layout.off_exn_bucket,
        Layout.domainStateBytes, Layout.off_ref_table] <;> omega

/-- **`RuntimeFrame` for the pinned F1 layout.** -/
theorem f1_runtimeFrame : RuntimeFrame Gc.f1Layout Gc.f1High Gc.f1Domain where
  domainWord _ ok := Gc.f1_domain ok
  stackHigh _ ok := Gc.f1_stackHigh ok
  windows _ vm := Gc.f1_stable (fun w hw => f1_vmWindow_apart (vm w hw)) fun w hw => f1_vmWindow_heapSafe (vm w hw)
  threshold _ ok := Gc.f1_threshold ok
  quiet _ ok := Gc.f1_quiet ok
  barrier _ ok := Gc.f1_trapBarrier ok
  backtrace _ ok := Gc.f1_backtrace ok

/-- The F1 runtime invariant depends on memory only. -/
theorem f1_memoryStable : MemoryStable Gc.f1Layout.runtimeOk :=
  fun _ _ memory ok => Gc.f1_sameMemory memory ok

end OCaml.Vm.Sim
