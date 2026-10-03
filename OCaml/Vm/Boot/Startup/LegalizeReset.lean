import Vsa.Machine

/-! Zero-valued reset CSRs: the read of misa must succeed, but its value does
not affect these legalization results. -/
open Vsa.Machine LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
namespace OCaml.Vm.Boot.Startup
theorem legalize_senvcfg_zero (s : MState) (m : BitVec 64) (hm : s.regs.get? .misa = some m) :
    (legalize_senvcfg 0 0).run s = .ok 0 s := by
  simp only [legalize_senvcfg, currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, hm,
    Mk_SEnvcfg, _get_SEnvcfg_CBZE, _get_SEnvcfg_CBCFE, _get_SEnvcfg_CBIE,
    _get_SEnvcfg_PMM, _get_SEnvcfg_LPE, _get_SEnvcfg_SSE, _get_SEnvcfg_FIOM,
    legalize_xenvcfg_cbie]
  rfl

theorem legalize_mseccfg_zero (s : MState) (m : BitVec 64) (hm : s.regs.get? .misa = some m) :
    (legalize_mseccfg 0 0).run s = .ok 0 s := by
  simp only [legalize_mseccfg, currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, hm,
    Mk_Seccfg, _get_Seccfg_USEED, _get_Seccfg_SSEED, _get_Seccfg_MLPE, _get_Seccfg_PMM]
  rfl

theorem legalize_menvcfg_zero (s : MState) (m : BitVec 64) (hm : s.regs.get? .misa = some m) :
    (legalize_menvcfg 0 0).run s = .ok 0 s := by
  simp only [legalize_menvcfg, currentlyEnabled, hartSupports]
  simp [simp_sail, EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    readReg, get, getThe, MonadStateOf.get, EStateM.get, hm,
    Mk_MEnvcfg, _get_MEnvcfg_PBMTE, _get_MEnvcfg_ADUE, _get_MEnvcfg_PMM, _get_MEnvcfg_STCE, _get_MEnvcfg_CBIE, _get_MEnvcfg_CBCFE, _get_MEnvcfg_CBZE, _get_MEnvcfg_SSE, _get_MEnvcfg_LPE, _get_MEnvcfg_FIOM, legalize_xenvcfg_cbie]
  rfl

end OCaml.Vm.Boot.Startup
