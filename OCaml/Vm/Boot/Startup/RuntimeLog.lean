import OCaml.Vm.Boot.Startup.RuntimeReady
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- A finite write log can update unowned runtime globals and live payloads
while retaining the common allocator/platform interface. -/
theorem RuntimeReady.disjoint_log {H capacity oldsp oldra before after writes log pc value regs sp ra}
    (ready : RuntimeReady H capacity oldsp oldra before)
    (post : WriteRegistersPost writes log before pc value regs after)
    (keys : KeysOK writes) (cover : ∀ n ∈ writes, n ∈ keysG regs) (gpFrame : 3 ∉ writes)
    (stack : gprGet after.σ 2 = some sp) (link : gprGet after.σ 1 = some ra) (aligned : ra.toNat % 4 = 0)
    (pins : ∀ pin ∈ VsaIris.Sym.allocText, OutL log pin.1)
    (domain : OutLRange log Layout.sym_Caml_state 8)
    (pool : OutLRange log Layout.sym_pool 8)
    (heap : ∀ a, vsaFoot H a → OutL log a) : RuntimeReady H capacity sp ra after := by
  apply ready.effect_framed post keys cover gpFrame stack link aligned
  · intro pin member
    rw [writeLog_out _ _ _ (pins pin member)]
  · rw [bytesT_writeLog_out _ domain]
    exact ready.domainWord
  · exact lpins8_writeLog ready.poolZero pool
  · intro a owned
    rw [writeLog_out _ _ _ (heap a owned)]
  · intro a present
    exact writeLog_present _ _ _ present
end OCaml.Vm.Boot.Startup
