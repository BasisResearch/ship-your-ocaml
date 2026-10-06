import OCaml.Vm.Sim.F1Frame
import OCaml.Vm.Sim.DivisionRows

/-!
# The F1 layout's raise-runtime facts

`RaiseRuntimeFrame` (DivisionRows) asks two things of a layout: no
channel-unlock hook, and runtime stability under VM windows together with the
native scratch window. For the pinned F1 layout the hook is the pin
`channelUnlock` and the scratch window lies above the allocator arena, apart
from every word `f1Runtime` reads. (`Caml_state->external_raise` is carried by
the invocation, `Invocation.externalRaise`.)
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives OCaml.Vm

/-- The native scratch window misses the whole F1 runtime footprint. -/
theorem nativeScratch_apart {D : InvocationData} (v : NativeValid D) :
    ∀ x ∈ Gc.f1Footprint, Gc.Apart (nativeScratch D) x := by
  have hh := v.headroom
  intro x hx
  simp only [Gc.f1Footprint, Gc.keptFootprint, Gc.youngWord, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  simp only [nativeScratch, nativeHeadroom, Vsa.Sim.DlHeap.heapEnd, Gc.f1Domain, Boot.WhileMinRuntime.domain,
    Boot.WhileMinRuntime.freeBlock, Layout.sym_bss_end, Layout.sym_caml_callback_depth, Layout.sym_impure_data,
    Layout.sym_oo_last_id, Layout.sym_errno, Layout.off_young_ptr, Layout.off_stack_high,
    Layout.off_stack_threshold, Layout.off_trap_barrier, Layout.off_backtrace_active] at *
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Gc.Apart] <;> omega

/-- **`RaiseRuntimeFrame` for the pinned F1 layout.** -/
theorem f1_raiseRuntimeFrame : RaiseRuntimeFrame Gc.f1Layout Gc.f1High Gc.f1Domain where
  hook _ ok := ok.freeListShape.channelUnlock
  scratch _ D v each := Gc.f1_stable fun w hw => by
    rcases each w hw with vm | rfl
    · exact f1_vmWindow_apart vm
    · exact nativeScratch_apart v

end OCaml.Vm.Sim
