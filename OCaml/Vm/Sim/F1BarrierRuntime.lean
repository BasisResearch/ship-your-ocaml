import OCaml.Vm.Sim.BarrierF1
import OCaml.Vm.Gc.F1Barrier

/-! `BarrierRuntime` for the pinned F1 layout, from the F1 heap invariant:
the collector is idle (`Gc.f1_gcIdle`), the remembered set is a `Table` whose
struct and next entry are separated from the payload (`Gc.f1_tableRuntime`),
and an insertion with room keeps the runtime (`Gc.f1_insert`). -/

namespace OCaml.Vm.Sim
set_option autoImplicit false

/-- **`BarrierRuntime` for the pinned F1 layout.** -/
theorem f1_barrierRuntime : BarrierRuntime Gc.f1Layout :=
  ⟨Gc.f1_gcIdle, fun _ ok => Gc.f1_tableRuntime ok, Gc.f1_insert⟩

end OCaml.Vm.Sim
