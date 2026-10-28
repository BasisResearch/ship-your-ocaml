import OCaml.Vm.Boot.Startup.MainArgv
import OCaml.Vm.Boot.Startup.GprsSame
import OCaml.Vm.Boot.Startup.CamlRetrySteps

namespace OCaml.Vm.Boot.Startup
set_option autoImplicit false
open Vsa.Machine Vsa.Sim

/-- caml_main's actual file descriptor and argv registers, supplied by startup. -/
structure LoadCaller (c : Config) : Prop where
  fd : gprGet c.σ 8 = some 3#64
  argv : gprGet c.σ 9 = some argvPtr

/-- Transport the loading caller through an actual native register frame. -/
theorem LoadCaller.frame {before after writes} (R : LoadCaller before)
    (G : GprsSame before after writes) (fd : 8 ∉ writes) (argv : 9 ∉ writes) : LoadCaller after :=
  ⟨G.get (by decide) (by decide) fd R.fd, G.get (by decide) (by decide) argv R.argv⟩

end OCaml.Vm.Boot.Startup
