import OCaml.Vm.Boot.Startup.TableStackFrame
import OCaml.Vm.Boot.Startup.TableThird
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The three words saved by the source table-function prologue. -/
structure TableSaved (s0 s1 : BitVec 64) (c : Config) : Prop where
  saved0 : bytesT c.σ.mem (firstMallocStack.toNat - 16) 8 = s0
  returnAddress : bytesT c.σ.mem (firstMallocStack.toNat - 8) 8 = jal_8002a934_call.link
  saved1 : bytesT c.σ.mem (firstMallocStack.toNat - 24) 8 = s1

/-- Each saved word is read back from its generated store-log entry. -/
theorem table_saved_after_prefix {before after : Config} {s0 s1 : BitVec 64}
    (memory : after.σ.mem = writeLog before.σ.mem (minorTablesLog s0 s1)) : TableSaved s0 s1 after := by
  constructor
  · rw [memory]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 0 _ _ rfl (by simp only [minorTablesLog, List.drop, OutLRange]; decide)
  · rw [memory]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 1 _ _ rfl (by simp only [minorTablesLog, List.drop, OutLRange]; decide)
  · rw [memory]
    exact OCaml.Vm.Gc.word_writeLog_at _ _ 2 _ _ rfl (by trivial)

theorem TableSaved.transport {s0 s1 before after} (h : TableSaved s0 s1 before)
    (frame : TableStackFrame before after) : TableSaved s0 s1 after :=
  ⟨(frame.word _ (by decide)).trans h.saved0,
   (frame.word _ (by decide)).trans h.returnAddress,
   (frame.word _ (by decide)).trans h.saved1⟩
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird : Config}

theorem ResetTableZeroed.saved
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    TableSaved ((gprGet atTables.σ 8).getD 0) ((gprGet atTables.σ 9).getD 0) afterZero := by
  have saved := table_saved_after_prefix w.published.allocation.before.request.post.memory
  have toMalloc := TableStackFrame.of_memory w.published.allocation.before.post.memory
  have allocated := allocator_table_stack_frame w.published.allocation.post
  have published := table_publish_stack_frame w.published.post
  have zeroed := table_zero_stack_frame w.published.allocation.region w.post
  exact saved.transport (toMalloc.trans (allocated.trans (published.trans zeroed)))

/-- All three actual malloc calls and both completed memsets preserve the
caller frame that the final tail path will restore. -/
theorem ResetThirdAllocation.saved
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    TableSaved ((gprGet atTables.σ 8).getD 0) ((gprGet atTables.σ 9).getD 0) afterThird := by
  obtain ⟨allocation⟩ := w.allocation
  exact w.first.saved.transport allocation.stack_frame
end OCaml.Vm.Boot.WhileMinElfParse
