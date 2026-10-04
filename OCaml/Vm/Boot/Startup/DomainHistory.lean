import OCaml.Vm.Boot.Startup.DomainReady
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup

/-- Pack the established domain execution history once, so subsequent callers
retain its exact effects without adding all earlier configurations as parameters. -/
structure DomainHistory (initial after : Config) where
  atMain : Config
  atDomain : Config
  atAlloc : Config
  atMalloc : Config
  afterMalloc : Config
  atTables : Config
  atRequest : Config
  atTableMalloc : Config
  afterTable : Config
  afterPublish : Config
  afterZero : Config
  afterThird : Config
  afterThirdPublish : Config
  returned : Config
  fieldsDone : Config
  witness : ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone after

theorem DomainHistory.reset {initial after} (h : DomainHistory initial after) : ElfResetReady elf initial :=
  h.witness.tables.third.first.published.allocation.before.request.tables.allocation.before.alloc.domain.main.reset

theorem domain_history_exists : ∃ initial after, Nonempty (DomainHistory initial after) := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, afterThird, afterThirdPublish, returned, fieldsDone, after, w⟩ := reset_domain_returned_exists
  exact ⟨initial, after, ⟨atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, afterThird, afterThirdPublish, returned, fieldsDone, w⟩⟩
end OCaml.Vm.Boot.WhileMinElfParse
