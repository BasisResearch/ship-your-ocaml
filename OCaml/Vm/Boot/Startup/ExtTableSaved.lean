import OCaml.Vm.Boot.Startup.ExtTableAllocate
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

theorem extTable_saved {sp ra s0 off value} (frame : NativeFrame sp 16) (mem : Vsa.MemRepr.Mem)
    (member : (off, value) ∈ [(0, s0), (8, ra)]) :
    bytesT (writeLog mem (extTableLog sp ra s0)) (nativeFrameBase sp 16 + off) 8 = value := by
  rw [extTableLog, writeLog_append, bytesT_writeLog_out _ (show OutLRange extTableHeader (nativeFrameBase sp 16 + off) 8 from ?_)]
  · apply frame.word_log_read (slots := [(0, s0), (8, ra)])
    · intro k v hk
      have choices : (k, v) = (0, s0) ∨ (k, v) = (8, ra) := by simpa using hk
      rcases choices with eq | eq <;> cases eq <;> decide
    · simp
    · exact member
  · have lower := frame.lower
    have bounds : Layout.sym_caml_shared_libs_path + Layout.off_ext_table_size + 4 ≤ heapEnd ∧
        Layout.sym_caml_shared_libs_path + Layout.off_ext_table_capacity + 4 ≤ heapEnd := by decide
    simp only [extTableHeader, OutLRange]
    exact ⟨Or.inr (by unfold nativeFrameBase; omega), Or.inr (by unfold nativeFrameBase; omega), trivial⟩

/-- The complete allocator call preserves either word of the ext_table caller. -/
theorem ExtTableAllocated.saved_word {H capacity sp ra s0 before after off value}
    (w : ExtTableAllocated H capacity sp ra s0 before after) (frame : NativeFrame sp 560)
    (member : (off, value) ∈ [(0, s0), (8, ra)]) :
    bytesT after.σ.mem (nativeFrameBase sp 16 + off) 8 = value := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  rw [word_observed (m := w.called.σ.mem) (nativeFrameBase sp 16 + off)
    (fun i hi => (w.allocation.caller_frame nested).byte _ (by rw [short.stack_nat]; omega)), w.call.memory, w.setup.memory]
  exact extTable_saved short _ member
end OCaml.Vm.Boot.Startup
