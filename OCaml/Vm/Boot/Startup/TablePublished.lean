import OCaml.Vm.Boot.Startup.TablePublish
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris VsaIris.Inst VsaIris.VsaHeap OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable : Config}

/-- Allocation and stack saves preserve the runtime's published domain pointer. -/
theorem ResetTableAllocation.domain_word
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    bytesT afterTable.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
  rw [word_observed (m := atTableMalloc.σ.mem) Layout.sym_Caml_state
    (fun i hi => w.post.memory _ (domain_allocator_outside _ _ (by decide) i hi)),
    w.before.post.memory, w.before.request.post.memory]
  rw [bytesT_writeLog_out _ (show OutLRange _ Layout.sym_Caml_state 8 from by
    simp only [minorTablesLog, OutLRange]; decide)]
  exact w.before.request.tables.prefixInput.domain

theorem ResetTableAllocation.publishInput
    (w : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable) :
    TablePublishInput (vsaReg afterTable 10) jal_80009828_call.link afterTable where
  toLeafInput := w.leaf
  globalReg := (w.saved 8 (by decide)).trans (gholds_lookup (n := 8) _ w.before.request.post.regs (by rfl))
  pointer := library_gpr w.post.good (by decide) (by decide) rfl
  domain := (w.saved 9 (by decide)).trans (gholds_lookup (n := 9) _ w.before.request.post.regs (by rfl))
  domainWord := w.domain_word
  nonzero := by
    intro eq
    have nonzero := w.post.result.fresh.nonzero
    exact nonzero (congrArg BitVec.toNat eq)

/-- The first table pointer is now published through the source instruction
sequence, with its exact domain-field write retained. -/
structure ResetTablePublished (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish : Config) : Prop where
  allocation : ResetTableAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable
  run : Steps (Vsa.Densify.fillZero initial) afterPublish
  post : WriteRegistersPost [15, 10] (tablePublishLog .refs (vsaReg afterTable 10)) afterTable
    MinorTableSlot.refs.exit (vsaReg afterTable 10) (tablePublishRegs (vsaReg afterTable 10)) afterPublish

theorem reset_table_published_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish,
    ResetTablePublished initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, w⟩ :=
    reset_table_allocation_exists
  obtain ⟨afterPublish, run, post⟩ := (table_publish afterTable .refs _ _ w.publishInput).run afterTable ⟨w.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    afterPublish, w, w.run.trans run, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
