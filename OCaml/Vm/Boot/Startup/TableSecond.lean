import OCaml.Vm.Boot.Startup.TableNextReturn
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Reset now returns from the second table allocation with the first table
retained in the live heap and a second charge spent. -/
structure ResetSecondAllocation (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterSecond : Config) : Prop where
  first : ResetTableZeroed initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero
  run : Steps (Vsa.Densify.fillZero initial) afterSecond
  allocation : Nonempty (TableNextAllocated (firstTableHeap (vsaReg afterTable 10))
    (startupAllocatorCredits - 128) false afterZero afterSecond)

theorem reset_second_allocation_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterSecond,
    ResetSecondAllocation initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterSecond := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, w⟩ :=
    reset_table_zeroed_exists
  have credits : startupAllocatorCredits - 64 = startupAllocatorCredits - 128 + 64 := by decide
  have ready := w.ready
  rw [credits] at ready
  obtain ⟨afterSecond, run, allocation⟩ := (table_next_allocate afterZero false _ _ _ ready).run afterZero ⟨w.post.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable,
    afterPublish, afterZero, afterSecond, w, w.run.trans run, allocation⟩
end OCaml.Vm.Boot.WhileMinElfParse
