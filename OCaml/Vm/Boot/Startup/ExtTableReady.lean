import OCaml.Vm.Boot.Startup.ExtTablePrefix
import OCaml.Vm.Boot.Startup.RuntimeWindows
import OCaml.Vm.Boot.Startup.StartupAuxMemory
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives

theorem sharedTable_outside_allocator {H a} (owned : vsaFoot H a) :
    a < Layout.sym_caml_shared_libs_path ∨ Layout.sym_caml_shared_libs_path + Layout.ext_table_bytes ≤ a := by
  unfold vsaFoot allocGlobal InRange at owned
  unfold Layout.sym_caml_shared_libs_path Layout.ext_table_bytes heapStart at *
  omega

theorem extTable_windows_byte {sp a} (frame : NativeFrame sp 16) (below : a < heapEnd)
    (table : a < Layout.sym_caml_shared_libs_path ∨ Layout.sym_caml_shared_libs_path + Layout.ext_table_bytes ≤ a) :
    OutW (extTableWindows sp) a := by
  have lower := frame.lower
  exact ⟨Or.inl (by change a < nativeFrameBase sp 16; unfold nativeFrameBase; omega), table, trivial⟩

theorem extTable_windows_range {sp a n} (frame : NativeFrame sp 16) (below : a + n ≤ heapEnd)
    (table : a + n ≤ Layout.sym_caml_shared_libs_path ∨ Layout.sym_caml_shared_libs_path + Layout.ext_table_bytes ≤ a) :
    OutWRange (extTableWindows sp) a n := by
  have lower := frame.lower
  exact ⟨Or.inl (by change a + n ≤ nativeFrameBase sp 16; unfold nativeFrameBase; omega), table, trivial⟩

theorem ext_table_prefix_ready {H capacity sp ra s0 before after}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp 16)
    (post : WriteRegistersPost [2, 8, 10] (extTableLog sp ra s0) before jal_80003dd4_call.pc 64#64
      (extTableRegs sp ra) after) : RuntimeReady H capacity (nativeStack sp 16) ra after := by
  apply ready.window_log post (by decide) (by simp only [extTableRegs, keysG]; decide) (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) ready.aligned (extTableLog_inside frame)
  · intro pin hp
    have source := allocator_sources pin hp
    have low := source.geometry.high
    have table := source.before_startup_count
    have bounds : heapStart ≤ heapEnd ∧ Layout.sym_startup_count ≤ Layout.sym_caml_shared_libs_path := by decide
    exact extTable_windows_byte frame (by omega) (Or.inl (by omega))
  · exact extTable_windows_range frame (by decide) (Or.inl (by decide))
  · exact extTable_windows_range frame (by decide) (Or.inl (by decide))
  · intro a owned
    exact extTable_windows_byte frame (allocator_foot_below owned) (sharedTable_outside_allocator owned)
end OCaml.Vm.Boot.Startup
