import OCaml.Vm.Boot.Startup.ConfigMemoryProgram

namespace OCaml.Vm.Boot.Startup
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1

theorem config_memory (s : MState) (h : s.regs.get? .pma_regions = some Vsa.Sim.initPmaRegions) :
    (check_mem_layout ()).run s = .ok true s := by
  have nonempty : (Vsa.Sim.initPmaRegions == []) = false := rfl
  rw [configMemoryProgram.eq]
  simp only [configMemoryProgram, EStateM.run, bind, EStateM.bind,
    readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, h, pure, EStateM.pure, nonempty, Bool.false_eq_true, ite_false, zeros, BitVec.zero, BitVec.ofNatLT_zero,
    ← resetPmaOptions.eq_def, resetPmas_valid, clint_window s h, signal_window s h]
  rfl
end OCaml.Vm.Boot.Startup
