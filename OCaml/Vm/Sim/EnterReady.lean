import OCaml.Vm.Sim.CheckSignals
import OCaml.Vm.Sim.ReadGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine

/-- The shared application tail can return directly to dispatch when the
current stack is above the runtime threshold and no pending work is set.
The full loop invariant must supply these read and capacity facts. -/
structure EnterReady (c : Config) (sp : Nat) : Prop extends SignalCheckReady c where
  threshold : RamReadAt ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold) 8
  capacity : (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)).toNat ≤ sp

end OCaml.Vm.Sim
