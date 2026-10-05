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
  intro v hv
  simp only [Gc.f1Footprint, Gc.keptFootprint, Gc.youngWord, List.mem_cons, List.not_mem_nil,
    or_false] at hv
  rcases vm with ⟨low, high⟩ | ⟨off, member, rfl⟩
  · simp only [Gc.f1High, Gc.f1Domain, Boot.WhileMinEntry.high, Boot.WhileMinRuntime.domain,
      Boot.WhileMinRuntime.freeBlock, Layout.stackBytes, Layout.sym_bss_end, Layout.off_young_ptr,
      Layout.off_stack_high, Layout.off_stack_threshold] at *
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Gc.Apart] <;> omega
  · simp only [vmDomainOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [Gc.f1Domain, Boot.WhileMinRuntime.domain, Boot.WhileMinRuntime.freeBlock, Layout.sym_bss_end,
      Layout.off_young_ptr, Layout.off_stack_high, Layout.off_stack_threshold] at *
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Gc.Apart, Layout.off_trapsp,
        Layout.off_extern_sp, Layout.off_local_roots, Layout.off_exn_bucket,
        Layout.off_external_raise] <;> omega

/-- **`RuntimeFrame` for the pinned F1 layout.** -/
theorem f1_runtimeFrame : RuntimeFrame Gc.f1Layout Gc.f1High Gc.f1Domain where
  domainWord _ ok := Gc.f1_domain ok
  stackHigh _ ok := Gc.f1_stackHigh ok
  windows _ vm := Gc.f1_stable fun w hw => f1_vmWindow_apart (vm w hw)
  threshold _ ok := Gc.f1_threshold ok
  quiet _ ok := Gc.f1_quiet ok

/-- The F1 runtime invariant depends on memory only. -/
theorem f1_memoryStable : MemoryStable Gc.f1Layout.runtimeOk :=
  fun c c' memory ok => Gc.f1_transfer (fun x n _ => by simp only [memory]) ok

end OCaml.Vm.Sim
