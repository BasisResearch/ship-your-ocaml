import Vsa.Sim.ValueSites

namespace Vsa.Sim
open LeanRV64DExecutable Sail
open Vsa.Machine (MState)

structure SiteGood (σ : MState) (pc : BitVec 64) : Prop where
  priv : (afterNextPC (afterPrelude σ) pc).regs.get? Register.cur_privilege
    = some (Privilege.Machine : RegisterType Register.cur_privilege)
  mstatus : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mstatus = some initMstatus
  seccfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.mseccfg = some (0#64)
  pma : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pma_regions
    = some (initPmaRegions : RegisterType Register.pma_regions)
  cfg : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpcfg_n
    = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n)
  pmpaddr : (afterNextPC (afterPrelude σ) pc).regs.get? Register.pmpaddr_n = some initPmpaddr
  tohost : (afterNextPC (afterPrelude σ) pc).regs.get? Register.htif_tohost_base
    = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base)

theorem siteGood_of_good (σ : MState) (pc : BitVec 64) (hG : GoodState σ) : SiteGood σ pc where
  priv := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.cur_privilege
  mstatus := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mstatus
  seccfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.mseccfg
  pma := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pma_regions
  cfg := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpcfg_n
  pmpaddr := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.pmpaddr_n
  tohost := by rw [get?_afterNextPC σ pc _ (by decide) (by decide)]; exact hG.htif_tohost_base

end Vsa.Sim
