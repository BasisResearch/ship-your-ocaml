import OCaml.Vm.Boot.Startup.CustomEntry
import OCaml.Vm.Boot.Startup.CustomAllocate
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup OCaml.Vm.Primitives

/-- Low BSS bytes outside initialized runtime globals retain their reset zero
through domain/tables, parameter parsing, startup count and locale setup. -/
theorem ResetCustomEntry.bss_byte {initial entry} (w : ResetCustomEntry initial entry) (a : Nat)
    (lo : Layout.sym_bss_start ≤ a) (hi : a < Layout.sym_bss_start + 8 * bssWords)
    (afterEnv : Layout.sym_environ + 8 ≤ a) (below : a < heapStart)
    (dataByte : StartupDataBytes a)
    (counter : a < Layout.sym_startup_count ∨ Layout.sym_startup_count + 4 ≤ a) :
    (entry.σ.mem[a]?).getD 0 = 0#8 := by
  have bound : heapStart ≤ Layout.sym_stack_top - 8 := by decide
  have initialZero : (w.auxiliary.parameter.entry.σ.mem[a]?).getD 0 = 0#8 := by
    rw [w.auxiliary.parameter.before.data_frame.byte a dataByte]
    apply w.auxiliary.parameter.before.domain.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.post.toCrtCamlMainPost.bss_byte a lo hi
    exact mainWrites_between _ _ _ afterEnv (by omega)
  have parserFrame : NativeFrame parameterStack 176 := by constructor <;> decide
  have parserZero : (w.auxiliary.source.σ.mem[a]?).getD 0 = 0#8 := by
    rw [w.auxiliary.parameter.post.memory,
      frameOn_writeLog _ _ _ (parameterPresentLog_inside parserFrame) a ?_]
    · exact initialZero
    · have lower : heapStart ≤ nativeFrameBase parameterStack 176 := by decide
      exact ⟨Or.inl (by dsimp only; omega), trivial⟩
  have auxFrame : NativeFrame parameterStack 16 := by constructor <;> decide
  have heapBound : heapStart ≤ heapEnd := by decide
  have auxCallMemory : w.auxiliary.called.σ.mem = w.auxiliary.source.σ.mem := w.auxiliary.call.memory
  have auxZero : (w.source.σ.mem[a]?).getD 0 = 0#8 := by
    rw [w.auxiliary.post.memory, startupAux_byte auxFrame _ a (by omega) counter, auxCallMemory]
    exact parserZero
  have localeFrame : NativeFrame camlMainStack Layout.camlMainFrameBytes := by constructor <;> decide
  rw [w.call.memory, w.locale.memory,
    frameOn_writeLog _ _ _ (camlLocaleLog_inside localeFrame) a ?_]
  · exact auxZero
  · have lower : heapStart ≤ nativeFrameBase camlMainStack Layout.camlMainFrameBytes := by decide
    exact ⟨Or.inl (by dsimp only; omega), trivial⟩

/-- The first custom list is empty because its BSS word is cleared and every
preceding native effect is disjoint; no captured-state premise is used. -/
theorem ResetCustomEntry.custom_head {initial entry} (w : ResetCustomEntry initial entry) :
    bytesT entry.σ.mem Layout.sym_custom_ops_table 8 = 0#64 := by
  have byte (i : Nat) (hi : i < 8) :
      (entry.σ.mem[Layout.sym_custom_ops_table + i]?).getD 0 = 0#8 := by
    apply w.bss_byte
    · unfold Layout.sym_bss_start Layout.sym_custom_ops_table; omega
    · unfold bssWords Layout.sym_bss_start Layout.sym_bss_end Layout.sym_custom_ops_table; omega
    · unfold Layout.sym_environ Layout.sym_custom_ops_table; omega
    · unfold heapStart Layout.sym_custom_ops_table; omega
    · apply Or.inl
      refine ⟨?_, ?_, ?_⟩
      · unfold heapStart Layout.sym_custom_ops_table; omega
      · intro owned
        exact customTable_allocator_outside (H := []) (by omega) (by omega) (Or.inl owned)
      · apply Or.inl
        unfold Layout.sym_custom_ops_table Layout.sym_Caml_state
        omega
    · apply Or.inr
      unfold Layout.sym_startup_count Layout.sym_custom_ops_table
      omega
  rw [word_observed (m := (∅ : Vsa.MemRepr.Mem)) Layout.sym_custom_ops_table (fun i hi => by simpa using byte i hi)]
  simp [bytesT]
end OCaml.Vm.Boot.WhileMinElfParse
