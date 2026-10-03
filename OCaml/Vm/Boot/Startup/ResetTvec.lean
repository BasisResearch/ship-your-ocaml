import OCaml.Vm.Boot.Startup.ResetPmp
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
namespace OCaml.Vm.Boot.Startup
/-- The configured direct-mode trap vectors are already at their reset values. -/
theorem reset_tvecs_run (s : MState)
    (hm : s.regs.get? .mtvec = some 0#64) (hs : s.regs.get? .stvec = some 0#64) :
    (reset_tvecs ()).run s = .ok () s := by
  have clear : ∀ v : BitVec 64, v = 0#64 →
      Sail.BitVec.updateSubrange v 1 0 (trapVectorMode_backwards .TV_Direct) = 0#64 := by
    intro v hv; subst v; rfl
  simp only [reset_tvecs, plat_mtvec_direct_mode_supported, plat_stvec_direct_mode_supported,
    ite_true, EStateM.run, Bind.bind, EStateM.bind,
    readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure, hm, clear _ rfl]
  rw [show writeReg .mtvec (0#64) s = .ok () s from writeReg_present s _ _ hm]
  simp only [hs, EStateM.pure, clear _ rfl]
  exact writeReg_present s _ _ hs
end OCaml.Vm.Boot.Startup
