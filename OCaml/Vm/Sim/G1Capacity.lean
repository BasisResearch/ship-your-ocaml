import OCaml.Vm.Sim.StackRows
import OCaml.Vm.Gc.G1RoomDefs

namespace OCaml.Vm.Sim
set_option autoImplicit false

/-- The G1 budget leaves both thresholds of slack on the VM stack. -/
theorem g1_capacity : StackCapacity Gc.g1Budget := by unfold StackCapacity; decide

end OCaml.Vm.Sim
