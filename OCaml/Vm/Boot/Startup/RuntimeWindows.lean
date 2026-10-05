import OCaml.Vm.Boot.Startup.RuntimeLog
import OCaml.Vm.Sim.LogWindow
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Window certificates share the proof that a mixed stack/global store log
preserves allocator ownership and protected runtime observations. -/
theorem RuntimeReady.window_log {H capacity oldsp oldra before after writes log pc value regs sp ra windows}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (inside : LogInW windows log)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, OutW windows pin.1)
    (domain : OutWRange windows Layout.sym_Caml_state 8)
    (pool : OutWRange windows Layout.sym_pool 8)
    (heap : ∀ a, vsaFoot H a → OutW windows a) : RuntimeReady H capacity sp ra after := by
  apply ready.effect_framed post keys cover gpFrame stack link aligned
  · intro pin member
    rw [frameOn_writeLog _ _ _ inside pin.1 (pins pin member)]
  · rw [bytesT_writeLog_out _ (OCaml.Vm.Sim.outLRange_of_windows inside domain)]
    exact ready.domainWord
  · exact lpins8_writeLog ready.poolZero (OCaml.Vm.Sim.outLRange_of_windows inside pool)
  · intro a owned
    rw [frameOn_writeLog _ _ _ inside a (heap a owned)]
  · intro a present
    exact writeLog_present _ _ _ present
end OCaml.Vm.Boot.Startup
