import OCaml.Vm.Boot.Startup.CustomNext
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst OCaml.Vm.Primitives

theorem CustomRegistered.region {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after) :
    ZeroPairRegion (vsaReg w.allocated 10).toNat 1 := by
  have r : ZeroPairRegion (vsaReg w.allocation.allocated 10).toNat 1 :=
    ⟨w.allocation.allocation.allocation.result.fresh.lo,
      w.allocation.allocation.allocation.result.fresh.hi,
      w.allocation.allocation.allocation.result.align⟩
  rw [w.allocatedEq] at r
  exact r

theorem CustomRegistered.head_word {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after) :
    bytesT after.σ.mem Layout.sym_custom_ops_table 8 = vsaReg w.allocated 10 := by
  rw [w.publication.memory]
  exact customPublish_read w.region _ (by simp [customCells])

theorem CustomRegistered.table_reg {H capacity kind sp s0 head before after}
    (w : CustomRegistered H capacity kind sp s0 head before after) :
    gprGet after.σ 8 = some customTable :=
  gholds_lookup (n := 8) _ w.publication.regs (by rfl)
end OCaml.Vm.Boot.Startup
