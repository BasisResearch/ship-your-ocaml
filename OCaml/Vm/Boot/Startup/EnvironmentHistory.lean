import OCaml.Vm.Boot.Startup.EnvironmentHistoryFrame
import OCaml.Vm.Boot.Startup.ParameterEntry
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem EnvironmentFrame.publish {slot p before after}
    (post : WriteRegistersPost [15, 10] (tablePublishLog slot p) before slot.exit p (tablePublishRegs p) after) :
    EnvironmentFrame before after := by
  constructor
  intro a ha
  rw [post.memory, writeLog_out _ _ _ ?_]
  change (a < slot.address.toNat ∨ slot.address.toNat + 8 ≤ a) ∧ True
  have bounds : Layout.sym_environ + 8 ≤ slot.address.toNat ∧
      slot.address.toNat + 8 ≤ Layout.sym_embedded_env := by cases slot <;> decide
  unfold EnvironmentBytes at ha
  exact ⟨by omega, trivial⟩

theorem TableNextAllocated.environment_frame {H capacity last before after}
    (w : TableNextAllocated H capacity last before after) : EnvironmentFrame before after :=
  (EnvironmentFrame.of_memory w.setup.memory).trans
    ((EnvironmentFrame.of_memory w.dispatch.memory).trans (EnvironmentFrame.allocator (by decide) w.allocation))

theorem TableNextInitialized.environment_frame {H capacity before after}
    (w : TableNextInitialized H capacity before after) : EnvironmentFrame before after :=
  w.allocation.environment_frame.trans ((EnvironmentFrame.publish w.publication).trans
    (EnvironmentFrame.zero w.allocation.region w.zeroing))

theorem TableFinalAllocated.environment_frame {H capacity before after}
    (w : TableFinalAllocated H capacity before after) : EnvironmentFrame before after :=
  w.initialized.environment_frame.trans w.allocation.environment_frame
end OCaml.Vm.Boot.Startup

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

theorem ResetTableZeroed.environment_frame
    (w : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero) :
    EnvironmentFrame atRequest afterZero :=
  (EnvironmentFrame.of_memory w.published.allocation.before.post.memory).trans
    ((EnvironmentFrame.allocator (by decide) w.published.allocation.post).trans
      ((EnvironmentFrame.publish w.published.post).trans (EnvironmentFrame.zero w.published.allocation.region w.post)))

theorem ResetThirdAllocation.environment_frame
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    EnvironmentFrame atRequest afterThird := by
  obtain ⟨a⟩ := w.allocation
  exact w.first.environment_frame.trans a.environment_frame

theorem ResetTablesReturn.environment_frame
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    EnvironmentFrame atRequest returned :=
  w.third.environment_frame.trans ((EnvironmentFrame.publish w.publication).trans (EnvironmentFrame.zero w.third.region w.post))
end OCaml.Vm.Boot.WhileMinElfParse

namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

theorem ResetDomainWitness.environment_frame (w : ResetDomainWitness initial atMain atDomain) :
    EnvironmentFrame atMain atDomain := by
  exact EnvironmentFrame.stack w.post.memory (by simp only [camlMainLog, LogInW, InsideW]; decide)

theorem ResetStatAllocWitness.environment_frame (w : ResetStatAllocWitness initial atMain atDomain atAlloc) :
    EnvironmentFrame atMain atAlloc := by
  apply w.domain.environment_frame.trans
  exact EnvironmentFrame.stack w.post.memory (by simp only [savedRaLog, LogInW, InsideW]; decide)

theorem ResetFirstAllocation.environment_frame
    (w : ResetFirstAllocation initial atMain atDomain atAlloc atMalloc afterMalloc) :
    EnvironmentFrame atMain afterMalloc :=
  w.before.alloc.environment_frame.trans ((EnvironmentFrame.of_memory w.before.post.memory).trans
    (EnvironmentFrame.allocator (by decide) w.post))

theorem ResetMinorTables.environment_frame
    (w : ResetMinorTables initial atMain atDomain atAlloc atMalloc afterMalloc atTables) :
    EnvironmentFrame atMain atTables := by
  apply w.allocation.environment_frame.trans
  apply EnvironmentFrame.of_log w.post.memory domainInit_log_inside
  intro a ha
  unfold EnvironmentBytes at ha
  change (a < Layout.sym_Caml_state ∨ Layout.sym_Caml_state + 8 ≤ a) ∧
    (a < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ a) ∧ True
  have geometry : Layout.sym_environ + 8 ≤ Layout.sym_Caml_state ∧
      Layout.sym_Caml_state + 8 ≤ Layout.sym_embedded_env ∧
      Layout.sym_environ + 8 ≤ firstDomainPtr.toNat ∧
      firstDomainPtr.toNat + 928 ≤ Layout.sym_embedded_env := by decide
  exact ⟨by omega, by omega, trivial⟩

theorem ResetTableAlloc.environment_frame
    (w : ResetTableAlloc initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest) :
    EnvironmentFrame atMain atRequest := by
  apply w.tables.environment_frame.trans
  exact EnvironmentFrame.stack w.post.memory (by simp only [minorTablesLog, LogInW, InsideW]; decide)

theorem ResetDomainReturned.environment_frame
    (w : ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone) :
    EnvironmentFrame atMain domainDone := by
  apply w.tables.third.first.published.allocation.before.request.environment_frame.trans
  apply w.tables.environment_frame.trans
  apply EnvironmentFrame.trans (middle := fieldsDone)
  · apply EnvironmentFrame.of_log w.fields.memory domainFields_log_inside
    intro a ha
    unfold EnvironmentBytes at ha
    change (a < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ a) ∧ True
    have geometry : Layout.sym_environ + 8 ≤ firstDomainPtr.toNat ∧
        firstDomainPtr.toNat + 928 ≤ Layout.sym_embedded_env := by decide
    exact ⟨by omega, trivial⟩
  · exact EnvironmentFrame.of_memory w.post.memory

theorem ResetParameterEntry.environment_frame {initial entry}
    (w : ResetParameterEntry initial entry) : EnvironmentFrame w.domain.atMain entry :=
  w.domain.witness.environment_frame.trans (EnvironmentFrame.of_memory w.post.memory)
end OCaml.Vm.Boot.WhileMinElfParse
