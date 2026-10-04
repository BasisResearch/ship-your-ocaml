import OCaml.Vm.Boot.Startup.TableTailZero
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird : Config}

theorem ResetThirdAllocation.publishInput
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    TablePublishInput (vsaReg afterThird 10) (tableNextCall true).link afterThird := by
  obtain ⟨a⟩ := w.allocation
  have credits : startupAllocatorCredits - 64 = ((startupAllocatorCredits - 192) + 64) + 64 := by decide
  have ready := w.first.ready
  rw [credits] at ready
  exact a.allocation.publishInput (a.initialized.ready ready (by simp [firstTableHeap, firstDomainHeap]))

theorem ResetThirdAllocation.region
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    Memset56Region (vsaReg afterThird 10).toNat := by
  obtain ⟨a⟩ := w.allocation
  exact a.allocation.region

theorem ResetThirdAllocation.pc
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    PCAt MinorTableSlot.customs.entry afterThird := by
  obtain ⟨a⟩ := w.allocation
  exact a.allocation.pc

theorem ResetThirdAllocation.stack
    (w : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird) :
    gprGet afterThird.σ 2 = some (firstMallocStack - 32#64) := by
  obtain ⟨a⟩ := w.allocation
  exact library_gpr a.allocation.allocation.good (by decide) (by decide) a.allocation.allocation.result.frame.sp

/-- All three minor-table allocations, publications and zeroing calls have
returned to the source caml_init_domain continuation, with its frame restored. -/
structure ResetTablesReturn (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned : Config) : Prop where
  third : ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird
  run : Steps (Vsa.Densify.fillZero initial) returned
  publication : WriteRegistersPost [15, 10] (tablePublishLog .customs (vsaReg afterThird 10)) afterThird
    MinorTableSlot.customs.exit (vsaReg afterThird 10) (tablePublishRegs (vsaReg afterThird 10)) afterThirdPublish
  post : RegistersPost [8, 1, 9, 12, 11, 2, 6, 14, 15, 13, 5]
    (memset56Memory afterThirdPublish.σ.mem (vsaReg afterThird 10).toNat) afterThirdPublish
    jal_8002a934_call.link (BitVec.ofNat 64 (vsaReg afterThird 10).toNat)
    (tableTailFinalRegs (vsaReg afterThird 10).toNat ((gprGet atTables.σ 8).getD 0) ((gprGet atTables.σ 9).getD 0)) returned

theorem reset_tables_return_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned,
    ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, afterThird, w⟩ :=
    reset_third_allocation_exists
  obtain ⟨afterThirdPublish, publicationRun, publication⟩ :=
    (table_publish afterThird .customs _ _ w.publishInput).run afterThird ⟨w.pc, rfl⟩
  have leaf : LeafInput (tableNextCall true).link afterThirdPublish :=
    ⟨publication.good, publication.image, publication.minstret,
      (publication.frame .x1 (by decide) (by decide)).trans w.publishInput.raReg,
      by decide, publication.tick⟩
  have pointer : gprGet afterThirdPublish.σ 10 = some (BitVec.ofNat 64 (vsaReg afterThird 10).toNat) := by
    change gpr afterThirdPublish 10 = _
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using publication.result
  have stack := (publication.frame .x2 (by decide) (by decide)).trans w.stack
  have saved := w.saved.transport (table_publish_stack_frame publication)
  obtain ⟨returned, returnRun, post⟩ :=
    (table_tail_zero afterThirdPublish _ _ _ _ w.region leaf stack pointer saved).run afterThirdPublish ⟨publication.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    afterPublish, afterZero, afterThird, afterThirdPublish, returned, w,
    w.run.trans (publicationRun.trans returnRun), publication, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
