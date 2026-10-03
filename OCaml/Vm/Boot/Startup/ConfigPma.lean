import Vsa.Machine
import Vsa.Sim.InitValues

/-! Validation of the fixed model PMA regions and configured device windows. -/
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
def resetPmaOptions : pma_check_opts :=
  {
    zama16b := true, ziccamoa := true, ziccamoc := true, ziccif := true,
    zicclsm := true, ziccrse := true, ssccptr := true, svadu := true }
theorem resetPmas_valid : check_pma_regions Vsa.Sim.initPmaRegions 0#64 0#64 resetPmaOptions false =
    (pure true : SailM Bool) := by rfl
theorem within_reset_pma (s : MState) (h : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions)
    (component : String) (addr size : BitVec 64) (region : PMA_Region)
    (found : matching_pma_region_bits_range Vsa.Sim.initPmaRegions addr size = some region)
    (kind : region.attributes.mem_type = MemoryRegionType.IOMemory) :
    (within_configured_pma_memory component (some MemoryRegionType.IOMemory) addr size).run s =
      .ok true s := by
  simp only [within_configured_pma_memory, EStateM.run, bind, EStateM.bind,
    readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, h, pure, EStateM.pure, found, kind]
  rfl

theorem clint_window (s : MState) (h : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions) :
    within_configured_pma_memory "CLINT (platform.clint)"
      (some MemoryRegionType.IOMemory) 33554432#64 786432#64 s = .ok true s :=
  within_reset_pma s h _ _ _ (Vsa.Sim.initPmaRegions[1]!) (by rfl) (by rfl)

theorem signal_window (s : MState) (h : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions) :
    within_configured_pma_memory "simple interrupt generator (platform.simple_interrupt_generator)"
      (some MemoryRegionType.IOMemory) 201326592#64 (zero_extend (m := 64) plat_sig_size) s = .ok true s :=
  within_reset_pma s h _ _ _ (Vsa.Sim.initPmaRegions[1]!) (by rfl) (by rfl)

theorem clint_address_bits : to_bits_checked (l := 64) 33554432 = (pure 33554432#64 : SailM (BitVec 64)) := by rfl
theorem clint_size_bits : to_bits_checked (l := 64) 786432 = (pure 786432#64 : SailM (BitVec 64)) := by rfl
theorem signal_address_bits : to_bits_checked (l := 64) 201326592 = (pure 201326592#64 : SailM (BitVec 64)) := by rfl
end OCaml.Vm.Boot.Startup
