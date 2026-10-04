import OCaml.Vm.Boot.Startup.StartupAuxMemory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

/-- Incrementing the runtime startup counter preserves allocator ownership,
read-only code/pins, the published domain and disabled-pooling facts. -/
theorem startup_aux_ready {H capacity sp ra before after}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp 16)
    (post : WriteRegistersPost [1, 2, 10, 12, 13, 14, 15] (startupAuxLog sp ra) before ra 1#64
      (startupAuxRegs sp ra) after) : RuntimeReady H capacity sp ra after := by
  apply ready.effect_framed post (by decide) (by simp only [startupAuxRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) ready.aligned
  · intro pin member
    have source := allocator_sources pin member
    have high := source.geometry.high
    have bound : heapStart ≤ heapEnd := by decide
    rw [startupAux_byte frame _ _ (by omega) (Or.inl source.before_startup_count)]
  · apply Eq.trans (Vsa.Sim.Boot.bytesT_local_eq (m' := before.σ.mem) Layout.sym_Caml_state 8 ?_) ready.domainWord
    intro i hi
    have geometry : Layout.sym_startup_count + 4 ≤ Layout.sym_Caml_state ∧ Layout.sym_Caml_state + 8 ≤ heapEnd := by decide
    exact startupAux_byte frame _ _ (by omega) (Or.inr (by omega))
  · apply lpins8_observed ready.poolZero
    intro i hi
    have geometry : Layout.sym_startup_count + 4 ≤ Layout.sym_pool ∧ Layout.sym_pool + 8 ≤ heapEnd := by decide
    rw [startupAux_byte frame _ _ (by omega) (Or.inr (by omega))]
  · intro a owned
    rw [startupAux_byte frame _ a (allocator_foot_below owned) (startup_count_outside_allocator owned)]
  · intro a present
    exact writeLog_present _ _ _ present
end OCaml.Vm.Boot.Startup
