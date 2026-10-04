import OCaml.Vm.Boot.Startup.StartupDataFrame
import OCaml.Vm.Boot.Startup.ParameterEntry
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem StartupDataFrame.publish {slot p before after}
    (post : WriteRegistersPost [15, 10] (tablePublishLog slot p) before slot.exit p (tablePublishRegs p) after) :
    StartupDataFrame before after := by
  constructor
  intro a ha
  rw [post.memory, writeLog_out _ _ _ ?_]
  change (a < slot.address.toNat ∨ slot.address.toNat + 8 ≤ a) ∧ True
  have bounds : Vsa.Sim.DlHeap.heapStart ≤ slot.address.toNat ∧
      slot.address.toNat + 8 ≤ Vsa.Sim.DlHeap.heapEnd := by cases slot <;> decide
  exact ⟨startupData_heap_outside ha bounds.1 bounds.2, trivial⟩

theorem TableNextAllocated.data_frame {H capacity last before after}
    (w : TableNextAllocated H capacity last before after) : StartupDataFrame before after :=
  (StartupDataFrame.of_memory w.setup.memory).trans
    ((StartupDataFrame.of_memory w.dispatch.memory).trans (StartupDataFrame.allocator (by decide) w.allocation))

theorem TableNextInitialized.data_frame {H capacity before after}
    (w : TableNextInitialized H capacity before after) : StartupDataFrame before after :=
  w.allocation.data_frame.trans ((StartupDataFrame.publish w.publication).trans
    (StartupDataFrame.zero w.allocation.region w.zeroing))

theorem TableFinalAllocated.data_frame {H capacity before after}
    (w : TableFinalAllocated H capacity before after) : StartupDataFrame before after :=
  w.initialized.data_frame.trans w.allocation.data_frame
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

theorem ResetTableZeroed.data_frame
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    StartupDataFrame atRequest afterZero :=
  (StartupDataFrame.of_memory w.published.allocation.before.post.memory).trans
    ((StartupDataFrame.allocator (by decide) w.published.allocation.post).trans
      ((StartupDataFrame.publish w.published.post).trans (StartupDataFrame.zero w.published.allocation.region w.post)))

theorem ResetThirdAllocation.data_frame
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    StartupDataFrame atRequest afterThird := by
  obtain ⟨a⟩ := w.allocation
  exact w.first.data_frame.trans a.data_frame

theorem ResetTablesReturn.data_frame
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    StartupDataFrame atRequest returned :=
  w.third.data_frame.trans ((StartupDataFrame.publish w.publication).trans (StartupDataFrame.zero w.third.region w.post))
end OCaml.Vm.Boot.WhileMinElfParse

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

theorem ResetDomainWitness.data_frame (w : ResetDomainWitness initial atMain atDomain) :
    StartupDataFrame atMain atDomain := by
  exact StartupDataFrame.stack w.post.memory (by simp only [camlMainLog, LogInW, InsideW]; decide)

theorem ResetStatAllocWitness.data_frame (w : ResetStatAllocWitness initial atMain atDomain atAlloc) :
    StartupDataFrame atMain atAlloc := by
  apply w.domain.data_frame.trans
  exact StartupDataFrame.stack w.post.memory (by simp only [savedRaLog, LogInW, InsideW]; decide)

theorem ResetFirstAllocation.data_frame
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc afterMalloc) :
    StartupDataFrame atMain afterMalloc :=
  w.before.alloc.data_frame.trans ((StartupDataFrame.of_memory w.before.post.memory).trans
    (StartupDataFrame.allocator (by decide) w.post))

theorem ResetMinorTables.data_frame
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    StartupDataFrame atMain atTables := by
  apply w.allocation.data_frame.trans
  apply StartupDataFrame.of_log w.post.memory domainInit_log_inside
  intro a ha
  change (a < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ a) ∧
    (a < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ a) ∧ True
  have geometry : Layout.sym_Caml_state + 8 ≤ Vsa.Sim.DlHeap.heapEnd := by decide
  have pointer := startupData_heap_outside ha
    (show Vsa.Sim.DlHeap.heapStart ≤ firstDomainPtr.toNat from by decide)
    (show firstDomainPtr.toNat + 928 ≤ Vsa.Sim.DlHeap.heapEnd from by decide)
  rcases ha with ⟨_, _, outside⟩ | ⟨lower, _⟩
  · exact ⟨outside, pointer, trivial⟩
  · exact ⟨Or.inr (by omega), pointer, trivial⟩

theorem ResetTableAlloc.data_frame
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    StartupDataFrame atMain atRequest := by
  apply w.tables.data_frame.trans
  exact StartupDataFrame.stack w.post.memory (by simp only [minorTablesLog, LogInW, InsideW]; decide)

theorem ResetDomainReturned.data_frame
    (w : ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone) :
    StartupDataFrame atMain domainDone := by
  apply w.tables.third.first.published.allocation.before.request.data_frame.trans
  apply w.tables.data_frame.trans
  apply StartupDataFrame.trans (middle := fieldsDone)
  · apply StartupDataFrame.of_log w.fields.memory domainFields_log_inside
    intro a ha
    exact ⟨startupData_heap_outside ha
      (show Vsa.Sim.DlHeap.heapStart ≤ firstDomainPtr.toNat from by decide)
      (show firstDomainPtr.toNat + 928 ≤ Vsa.Sim.DlHeap.heapEnd from by decide), trivial⟩
  · exact StartupDataFrame.of_memory w.post.memory

theorem ResetParameterEntry.data_frame {initial entry}
    (w : ResetParameterEntry initial entry) : StartupDataFrame w.domain.atMain entry :=
  w.domain.witness.data_frame.trans (StartupDataFrame.of_memory w.post.memory)
/-- The original environment projection is a client of the broader startup data frame. -/
theorem ResetParameterEntry.environment_frame {initial entry}
    (w : ResetParameterEntry initial entry) : EnvironmentFrame w.domain.atMain entry :=
  w.data_frame.environment
end OCaml.Vm.Boot.WhileMinElfParse
