import OCaml.Vm.Boot.Startup.ExtTablePrefix
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.StartupAuxMemory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem extTable_windows_byte {sp t a} (frame : NativeFrame sp 16) (below : a < heapEnd)
    (table : a < t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ a) :
    OutW (extTableWindows sp t) a := by
  have lower := frame.lower
  exact ⟨Or.inl (by change a < nativeFrameBase sp 16; unfold nativeFrameBase; omega), table, trivial⟩

theorem extTable_windows_range {sp t a n} (frame : NativeFrame sp 16) (below : a + n ≤ heapEnd)
    (table : a + n ≤ t.toNat ∨ t.toNat + Layout.ext_table_bytes ≤ a) :
    OutWRange (extTableWindows sp t) a n := by
  have lower := frame.lower
  exact ⟨Or.inl (by change a + n ≤ nativeFrameBase sp 16; unfold nativeFrameBase; omega), table, trivial⟩

theorem ext_table_prefix_ready {H capacity sp ra s0 t n before after}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp 16) (site : ExtTableSite sp t)
    (post : WriteRegistersPost [2, 8, 10] (extTableLog sp ra s0 t n) before jal_80003dd4_call.pc
      (extTableRequest n) (extTableRegs sp ra t n) after) :
    RuntimeReady H capacity (nativeStack sp 16) ra after := by
  apply ready.window_log post (by decide) (by simp only [extTableRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) ready.aligned (extTableLog_inside frame)
  · intro pin hp
    have source := allocator_sources pin hp
    have low := source.before_startup_count
    have bounds : Layout.sym_startup_count ≤ heapEnd := by decide
    exact extTable_windows_byte frame (by omega) (Or.inl (site.pin frame low))
  · have geometry : Layout.sym_Caml_state + 8 ≤ heapEnd := by decide
    rcases site.domain frame with h | h
    · exact extTable_windows_range frame geometry (Or.inr h)
    · exact extTable_windows_range frame geometry (Or.inl h)
  · have geometry : Layout.sym_pool + 8 ≤ heapEnd := by decide
    rcases site.pool frame with h | h
    · exact extTable_windows_range frame geometry (Or.inr h)
    · exact extTable_windows_range frame geometry (Or.inl h)
  · intro a owned
    exact extTable_windows_byte frame (allocator_foot_below owned) (site.foot frame owned)
end OCaml.Vm.Boot.Startup
