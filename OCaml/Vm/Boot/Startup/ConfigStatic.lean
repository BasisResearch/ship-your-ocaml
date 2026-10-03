import Vsa.Machine

/-! The state-independent configuration checks used by Sail reset. -/
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions
namespace OCaml.Vm.Boot.Startup
theorem config_privs : check_privs () = (pure true : SailM Bool) := by rfl
theorem config_tvecs : check_tvecs () = (pure true : SailM Bool) := by rfl
theorem config_mstatus_fields : check_mstatus_fields () = (pure true : SailM Bool) := by rfl
theorem config_physaddr_bits : check_physaddr_bits () = (pure true : SailM Bool) := by rfl
theorem config_mmu_config : check_mmu_config () = (pure true : SailM Bool) := by rfl
theorem config_mmio_devices : check_mmio_devices () = (pure true : SailM Bool) := by rfl
theorem config_vlen_elen : check_vlen_elen () = (pure true : SailM Bool) := by rfl
theorem config_vext_config : check_vext_config () = (pure true : SailM Bool) := by
  simp [hartSupports, check_vext_config, vector_support_ge, vector_support_level, num_of_vector_support,
    Functions.elen_exp, Functions.not]
theorem config_pmp : check_pmp () = (pure true : SailM Bool) := by rfl
theorem config_misc_extension_dependencies : check_misc_extension_dependencies () = (pure true : SailM Bool) := by
  simp [hartSupports, check_required_sstvala_option, load_page_fault_writes_xtval, load_access_fault_writes_xtval,
    misaligned_load_writes_xtval, samo_page_fault_writes_xtval, samo_access_fault_writes_xtval,
    misaligned_samo_writes_xtval, fetch_page_fault_writes_xtval, fetch_access_fault_writes_xtval,
    misaligned_fetch_writes_xtval, hardware_breakpoint_writes_xtval,
    illegal_instruction_writes_xtval, sys_writable_hpm_counters, sys_scounteren_writable_bits,
    check_misc_extension_dependencies, vector_support_ge, vector_support_level,
    num_of_vector_support, Functions.not]
theorem config_extension_param_constraints : check_extension_param_constraints () = (pure true : SailM Bool) := by rfl
theorem config_version_constraints : check_version_constraints () = (pure true : SailM Bool) := by rfl
theorem config_stateen_config : check_stateen_config () = (pure true : SailM Bool) := by rfl
end OCaml.Vm.Boot.Startup
