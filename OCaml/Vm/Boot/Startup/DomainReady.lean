import OCaml.Vm.Boot.Startup.DomainReturned
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config}

/-- The full allocator and machine contract survives the table epilogue's
restoration of a different caller stack and saved-register assignment. -/
theorem ResetTablesReturn.ready
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
      RuntimeReady H (startupAllocatorCredits - 192) firstMallocStack jal_8002a934_call.link returned := by
  obtain ⟨a⟩ := w.third.allocation
  have credits : startupAllocatorCredits - 64 = (startupAllocatorCredits - 192) + 128 := by decide
  have first := w.third.first.ready
  rw [credits] at first
  have ready := a.ready first (by simp [firstTableHeap, firstDomainHeap])
  have domain : (firstDomainPtr.toNat, 928) ∈
      ((vsaReg afterThird 10).toNat, 56) :: ((vsaReg a.initialized.allocated 10).toNat, 56) :: firstTableHeap (vsaReg afterTable 10) := by
    simp [firstTableHeap, firstDomainHeap]
  have published := ready.publish domain w.publication
  refine ⟨_, domain, ?_⟩
  exact published.toRuntimeReady.zero w.post (by decide)
    (by simp only [tableTailFinalRegs, List.cons_append, List.nil_append, memset56Regs, keysG]; decide)
    (by decide) (gholds_lookup _ w.post.regs (by rfl)) (gholds_lookup _ w.post.regs (by rfl))
    (by decide) (by simp) w.third.region

/-- Complete domain initialization retains heap capacity, executable image,
all machine registers, idle HTIF, runtime globals and allocator read-only pins. -/
theorem ResetDomainReturned.ready
    (w : ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone) :
    ∃ H, (firstDomainPtr.toNat, 928) ∈ H ∧
      RuntimeReady H (startupAllocatorCredits - 192) (firstMallocStack + 16#64) jal_80004d94_call.link domainDone := by
  obtain ⟨H, domain, ready⟩ := w.tables.ready
  have stack : gprGet fieldsDone.σ 2 = some firstMallocStack :=
    (w.fields.frame .x2 (by decide) (by decide)).trans ready.stack
  have link : gprGet fieldsDone.σ 1 = some jal_8002a934_call.link :=
    (w.fields.frame .x1 (by decide) (by decide)).trans ready.raReg
  have fields := ready.payload_log w.fields (by decide)
    (by simp only [keysG, domainFieldsRegs]; decide) (by decide) stack link (by decide)
    domain (by decide) domainFields_log_inside
  refine ⟨H, domain, ?_⟩
  apply fields.effect w.post (by decide) (by simp only [keysG, domainReturnRegs]; decide) (by decide)
    (gholds_lookup _ w.post.regs (by rfl)) (gholds_lookup _ w.post.regs (by rfl)) (by decide)
  · intro a ha
    rfl
  · intro a ha
    rfl
  · intro a ha
    exact ha
end OCaml.Vm.Boot.WhileMinElfParse
