import OCaml.Vm.Boot.Startup.TableFinalAllocate
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Actual reset reaches the third table malloc return, after completely
initializing the first and second tables through their native calls. -/
structure ResetThirdAllocation (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird : Config) : Prop where
  first : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero
  run : Steps (Vsa.Densify.fillZero initial) afterThird
  allocation : Nonempty (TableFinalAllocated (firstTableHeap (vsaReg afterTable 10))
    (startupAllocatorCredits - 192) afterZero afterThird)

theorem reset_third_allocation_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird,
    ResetThirdAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, w⟩ :=
    reset_table_zeroed_exists
  have credits : startupAllocatorCredits - 64 = startupAllocatorCredits - 192 + 128 := by decide
  have ready := w.ready
  rw [credits] at ready
  obtain ⟨afterThird, run, allocation⟩ := (table_final_allocate afterZero _ _ _ ready
    (by simp [firstTableHeap, firstDomainHeap])).run afterZero ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    afterPublish, afterZero, afterThird, w, w.run.trans run, allocation⟩
end OCaml.Vm.Boot.WhileMinElfParse
