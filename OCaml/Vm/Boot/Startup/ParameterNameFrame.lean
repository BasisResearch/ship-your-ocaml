import OCaml.Vm.Boot.Startup.ParameterNames
import OCaml.Vm.Boot.Startup.NativeFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Sim

/-- Both source variable names lie below every valid native stack frame. -/
theorem parameter_name_below (fallback : Bool) {sp size} (frame : NativeFrame sp size) :
    (parameterName fallback).toNat + (parameterChars fallback).length + 1 ≤ nativeFrameBase sp size := by
  have bound : (parameterName fallback).toNat + (parameterChars fallback).length + 1 ≤ DlHeap.heapEnd := by
    cases fallback <;> decide
  have lower := frame.lower
  unfold nativeFrameBase
  omega
end OCaml.Vm.Boot.Startup
