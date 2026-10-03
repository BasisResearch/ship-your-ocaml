import OCaml.Vm.Boot.Startup.ConfigPma
import Vsa.Meta.SimpNF

namespace OCaml.Vm.Boot.Startup
open LeanRV64DExecutable LeanRV64DExecutable.Functions

-- Normalize the closed integer conversions before state-level composition.
#simp_nf configMemoryProgram : check_mem_layout () using [check_mem_layout,
  clint_address_bits, clint_size_bits, signal_address_bits, pure_bind]

end OCaml.Vm.Boot.Startup
