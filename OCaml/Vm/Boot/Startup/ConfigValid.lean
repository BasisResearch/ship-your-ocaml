import OCaml.Vm.Boot.Startup.ConfigStatic
import OCaml.Vm.Boot.Startup.ConfigMemory

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions

/-- Every state-independent guard is true; only the PMA check remains. -/
theorem config_valid_program : config_is_valid () = check_mem_layout () := by
  simp [config_is_valid, config_privs, config_tvecs, config_mstatus_fields,
    config_physaddr_bits, config_mmu_config, config_mmio_devices, config_vlen_elen,
    config_vext_config, config_pmp, config_misc_extension_dependencies,
    config_extension_param_constraints, config_version_constraints, config_stateen_config]

/-- The runner's model configuration validates successfully and leaves state unchanged. -/
theorem config_valid (s : MState) (h : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions) :
    (config_is_valid ()).run s = .ok true s := by
  rw [config_valid_program]
  exact config_memory s h

end OCaml.Vm.Boot.Startup
