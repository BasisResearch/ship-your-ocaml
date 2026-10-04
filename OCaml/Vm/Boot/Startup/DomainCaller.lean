import OCaml.Vm.Boot.Startup.TablesReturn
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast OCaml.Vm.Primitives

def domainCallerSlot : Nat := firstMallocStack.toNat + 8

theorem firstMalloc_caller_outside (i : Nat) (hi : i < 8) :
    ¬ mS [] firstMallocStack (domainCallerSlot + i) := by
  change ¬ (stackWin firstMallocStack allocHeadroom _ ∨ vsaFoot [] _)
  have addr : firstMallocStack.toNat = Layout.sym_stack_top - 144 := by decide
  simp only [stackWin, InExt, vsaFoot, allocGlobal, InRange, domainCallerSlot, addr,
    Layout.sym_stack_top, allocHeadroom, heapStart, heapEnd]
  omega
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

theorem ResetFirstAllocation.caller_word {initial atMain atDomain atAlloc atMalloc after : Config}
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc after) :
    bytesT after.σ.mem domainCallerSlot 8 = jal_80004d94_call.link := by
  rw [word_observed (m := atMalloc.σ.mem) domainCallerSlot
    (fun i hi => w.post.memory _ (firstMalloc_caller_outside i hi)), w.before.post.memory, w.before.alloc.post.memory]
  have address : (camlMainStack - 112#64 - 8#64).toNat = domainCallerSlot := by decide
  simp only [savedRaLog, address]
  exact word_writeLog _ _ _

theorem ResetMinorTables.caller_word {initial atMain atDomain atAlloc atMalloc afterMalloc atTables : Config}
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    bytesT atTables.σ.mem domainCallerSlot 8 = jal_80004d94_call.link := by
  rw [w.post.memory]
  apply Eq.trans (Vsa.Sim.Boot.bytesT_local_eq (m' := afterMalloc.σ.mem) domainCallerSlot 8 ?_) w.allocation.caller_word
  intro i hi
  apply frameOn_writeLog _ _ _ domainInit_log_inside
  change (domainCallerSlot + i < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ domainCallerSlot + i) ∧
    (domainCallerSlot + i < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ domainCallerSlot + i) ∧ True
  have bounds : Layout.sym_Caml_state + 8 ≤ domainCallerSlot ∧ firstDomainPtr.toNat + 928 ≤ domainCallerSlot := by decide
  exact ⟨Or.inr (by omega), Or.inr (by omega), trivial⟩

theorem ResetTableAlloc.caller_word {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest : Config}
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    bytesT atRequest.σ.mem domainCallerSlot 8 = jal_80004d94_call.link := by
  rw [w.post.memory, bytesT_writeLog_out _ (show OutLRange _ domainCallerSlot 8 from by
    simp only [minorTablesLog, OutLRange]; decide)]
  exact w.tables.caller_word

variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned : Config}

theorem ResetTableZeroed.stack_frame
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    TableStackFrame atRequest afterZero :=
  (TableStackFrame.of_memory w.published.allocation.before.post.memory).trans
    ((allocator_table_stack_frame w.published.allocation.post).trans
      ((table_publish_stack_frame w.published.post).trans (table_zero_stack_frame w.published.allocation.region w.post)))

theorem ResetThirdAllocation.stack_frame
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    TableStackFrame atRequest afterThird := by
  obtain ⟨a⟩ := w.allocation
  exact w.first.stack_frame.trans a.stack_frame

theorem ResetTablesReturn.stack_frame
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    TableStackFrame atRequest returned :=
  w.third.stack_frame.trans ((table_publish_stack_frame w.publication).trans (table_zero_stack_frame w.third.region w.post))

/-- The domain epilogue's return word is the actual link saved before its first
malloc, preserved through all intervening table operations. -/
theorem ResetTablesReturn.caller_word
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    bytesT returned.σ.mem domainCallerSlot 8 = jal_80004d94_call.link :=
  (w.stack_frame.word _ (by decide)).trans w.third.first.published.allocation.before.request.caller_word
end OCaml.Vm.Boot.WhileMinElfParse
