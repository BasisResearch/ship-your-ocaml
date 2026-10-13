import OCaml.Vm.Sim.F1Console

/-! A store just below the native stack pointer (above the allocator arena)
keeps the F1 runtime invariant: the F1 instance of the `nativeStable` premise
of `prim_caml_string_notequal_returns`. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Vm.Primitives

theorem f1_native_stable :
    ∀ lo, Vsa.Sim.DlHeap.heapEnd ≤ lo → WindowStable Gc.f1Layout.runtimeOk [⟨lo, lo + 8⟩] :=
  fun lo h => Gc.f1_window (native_safe (lo := lo) (hi := lo + 8) h).1 (native_safe h).2

end OCaml.Vm.Sim
