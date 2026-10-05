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
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **`RuntimeFrame` for the pinned F1 layout.** -/
theorem f1_runtimeFrame : RuntimeFrame Gc.f1Layout Gc.f1High where
  stackHigh _ ok := Gc.f1_stackHigh ok
  stackWindow _ _ low high := Gc.f1_stackWindow low high
  threshold _ ok := Gc.f1_threshold ok
  quiet _ ok := Gc.f1_quiet ok

/-- The F1 runtime invariant depends on memory only. -/
theorem f1_memoryStable : MemoryStable Gc.f1Layout.runtimeOk :=
  fun c c' memory ok => Gc.f1_transfer (fun x n _ => by simp only [memory]) ok

end OCaml.Vm.Sim
