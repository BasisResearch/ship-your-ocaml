import OCaml.Vm.Boot.Startup.ParameterReset
import OCaml.Vm.Boot.Startup.StartupDataFrame
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris.VsaHeap OCaml.Vm.Primitives

/-- The once-only startup flags occupy this generated BSS interval. -/
def StartupControlByte (a : Nat) : Prop :=
  Layout.sym_shutdown_happened ≤ a ∧ a < Layout.sym_caml_cleanup_on_exit + 4

theorem startupControl_data {a} (ha : StartupControlByte a) : StartupDataBytes a := by
  apply Or.inl
  unfold StartupControlByte Layout.sym_shutdown_happened Layout.sym_caml_cleanup_on_exit at ha
  simp only [allocGlobal, InRange]
  unfold heapStart Layout.sym_Caml_state
  exact ⟨by omega, by omega, Or.inl (by omega)⟩

/-- The abstract BSS clear establishes any separated initial byte. -/
theorem CrtCamlMainPost.bss_byte {initial after} (post : CrtCamlMainPost initial after) (a : Nat)
    (lo : Layout.sym_bss_start ≤ a) (hi : a < Layout.sym_bss_start + 8 * bssWords)
    (outside : OutL (mainWrites 0x8000003c#64 (read8 initial.σ.mem Layout.sym_embedded_env)) a) :
    (after.σ.mem[a]?).getD 0 = 0#8 := by
  rw [post.memory, writeLog_out _ _ _ outside, clearWords_inside _ _ _ _ lo hi]
  rfl

theorem CrtCamlMainPost.startup_control {initial after} (post : CrtCamlMainPost initial after)
    (a : Nat) (ha : StartupControlByte a) : (after.σ.mem[a]?).getD 0 = 0#8 := by
  have bounds : Layout.sym_bss_start ≤ Layout.sym_shutdown_happened ∧
      Layout.sym_caml_cleanup_on_exit + 4 ≤ Layout.sym_bss_start + 8 * bssWords ∧
      Layout.sym_environ + 8 ≤ Layout.sym_shutdown_happened ∧
      Layout.sym_caml_cleanup_on_exit + 4 ≤ Layout.sym_stack_top - 8 := by decide
  unfold StartupControlByte at ha
  apply post.bss_byte a (by omega) (by omega)
  exact mainWrites_between _ _ _ (by omega) (by omega)
/-- Four zero total-byte observations supply a native signed-word load. -/
theorem lpins4_zero_of_bytes {c : Config} {a : Nat}
    (bytes : ∀ i, i < 4 → (c.σ.mem[a + i]?).getD 0 = 0#8) :
    LPins4 c.σ.mem a (List.replicate 4 0#8) :=
  ⟨bytes 0 (by decide), bytes 1 (by decide), bytes 2 (by decide), bytes 3 (by decide)⟩

structure StartupControls (c : Config) : Prop where
  shutdown : LPins4 c.σ.mem Layout.sym_shutdown_happened (List.replicate 4 0#8)
  count : LPins4 c.σ.mem Layout.sym_startup_count (List.replicate 4 0#8)
  cleanup : LPins4 c.σ.mem Layout.sym_caml_cleanup_on_exit (List.replicate 4 0#8)

end OCaml.Vm.Boot.Startup
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives

theorem ResetParameterEntry.startup_control {initial entry} (w : ResetParameterEntry initial entry)
    (a : Nat) (ha : StartupControlByte a) : (entry.σ.mem[a]?).getD 0 = 0#8 := by
  rw [w.data_frame.byte a (startupControl_data ha)]
  exact w.domain.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.post.toCrtCamlMainPost.startup_control a ha

theorem ResetParameterReturned.startup_control {initial after} (w : ResetParameterReturned initial after)
    (a : Nat) (ha : StartupControlByte a) : (after.σ.mem[a]?).getD 0 = 0#8 := by
  have frame : NativeFrame parameterStack 176 := by constructor <;> decide
  rw [w.post.memory, frameOn_writeLog _ _ _ (parameterPresentLog_inside frame) a ?_]
  · exact w.before.startup_control a ha
  · have bound : Layout.sym_caml_cleanup_on_exit + 4 ≤ nativeFrameBase parameterStack 176 := by decide
    exact ⟨Or.inl (by unfold StartupControlByte at ha; dsimp only; omega), trivial⟩
theorem ResetParameterReturned.controls {initial after} (w : ResetParameterReturned initial after) :
    StartupControls after := by
  have pins (base : Nat) (lo : Layout.sym_shutdown_happened ≤ base)
      (hi : base + 4 ≤ Layout.sym_caml_cleanup_on_exit + 4) :
      LPins4 after.σ.mem base (List.replicate 4 0#8) := by
    apply lpins4_zero_of_bytes
    intro i bound
    exact w.startup_control _ ⟨by omega, by omega⟩
  exact ⟨pins _ (by decide) (by decide), pins _ (by decide) (by decide), pins _ (by decide) (by decide)⟩
end OCaml.Vm.Boot.WhileMinElfParse
