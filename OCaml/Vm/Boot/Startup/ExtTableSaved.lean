import OCaml.Vm.Boot.Startup.ExtTableAllocate
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

theorem extTable_saved {sp ra s0 t n off value} (frame : NativeFrame sp 16) (site : ExtTableSite sp t)
    (mem : Vsa.MemRepr.Mem) (member : (off, value) ∈ [(0, s0), (8, ra)]) :
    bytesT (writeLog mem (extTableLog sp ra s0 t n)) (nativeFrameBase sp 16 + off) 8 = value := by
  rw [extTableLog, writeLog_append, bytesT_writeLog_out _ (show OutLRange (extTableHeader t n) (nativeFrameBase sp 16 + off) 8 from ?_)]
  · apply frame.word_log_read (slots := [(0, s0), (8, ra)])
    · intro k v hk
      have choices : (k, v) = (0, s0) ∨ (k, v) = (8, ra) := by simpa using hk
      rcases choices with eq | eq <;> cases eq <;> decide
    · simp
    · exact member
  · have small : off ≤ 8 := by
      have choices : (off, value) = (0, s0) ∨ (off, value) = (8, ra) := by simpa using member
      rcases choices with eq | eq <;> cases eq <;> decide
    have lower := frame.lower
    have place := site.frame frame
    simp only [extTableHeader, OutLRange]
    unfold nativeFrameBase Layout.off_ext_table_size Layout.off_ext_table_capacity Layout.ext_table_bytes at *
    refine ⟨?_, ?_, trivial⟩ <;> omega

/-- The complete allocator call preserves either word of the ext_table caller. -/
theorem ExtTableAllocated.saved_word {H capacity sp ra s0 t n before after off value}
    (w : ExtTableAllocated H capacity sp ra s0 t n before after) (frame : NativeFrame sp 560)
    (site : ExtTableSite sp t) (member : (off, value) ∈ [(0, s0), (8, ra)]) :
    bytesT after.σ.mem (nativeFrameBase sp 16 + off) 8 = value := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  rw [word_observed (m := w.called.σ.mem) (nativeFrameBase sp 16 + off)
    (fun i hi => (w.allocation.caller_frame nested).byte _ (by rw [short.stack_nat]; omega)), w.call.memory, w.setup.memory]
  exact extTable_saved short site _ member

/-- The complete allocator call preserves the table header it just wrote. -/
theorem ExtTableAllocated.header_byte {H capacity sp ra s0 t n before after a}
    (w : ExtTableAllocated H capacity sp ra s0 t n before after) (frame : NativeFrame sp 560)
    (site : ExtTableSite sp t) (lo : t.toNat ≤ a) (hi : a < t.toNat + Layout.ext_table_bytes) :
    (after.σ.mem[a]?).getD 0 = (w.called.σ.mem[a]?).getD 0 := by
  have short := frame.resize (small := 16) (by decide) (by decide)
  have nested : NativeFrame (nativeStack sp 16) 544 := frame.nested (front := 16) (by decide)
  rcases site.place with ⟨above, _⟩ | g
  · exact (w.allocation.caller_frame nested).byte _ (by rw [short.stack_nat]; unfold nativeFrameBase; omega)
  · apply w.allocation.framed_byte nested
    · have := g.high; unfold heapStart heapEnd at *; omega
    · intro owned
      rcases site.foot short owned with h | h <;> omega
end OCaml.Vm.Boot.Startup
