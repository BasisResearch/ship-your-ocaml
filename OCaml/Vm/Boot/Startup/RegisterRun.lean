import OCaml.Vm.Boot.Startup.RegisterValues
import Vsa.Sim.ReifyRegisterWrites

namespace OCaml.Vm.Boot.Startup
#reify_register_fragments registerValues as registerWrites

/-- All source register-write fragments execute by one reusable list induction. -/
theorem register_tail_run (s : Vsa.Machine.MState) :
    (registerValues.chunk100).run s = .ok ()
      (Vsa.Sim.RegisterWrites.apply registerWrites.entries100 s) := by
  rw [registerWrites.program100]
  exact Vsa.Sim.RegisterWrites.run _ _

end OCaml.Vm.Boot.Startup
