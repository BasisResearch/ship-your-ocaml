import OCaml.Vm.Boot.Startup.DomainComplete
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives

/-- Domain initialization, including its three allocated tables, returns to
caml_main along the actual reset execution. -/
structure ResetDomainReturned (initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone : Config) : Prop where
  tables : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned
  run : Steps (Vsa.Densify.fillZero initial) domainDone
  fields : WriteRegistersPost [15, 14] domainFieldsLog returned 0x8002a9d0#64
    (BitVec.ofNat 64 (vsaReg afterThird 10).toNat) (domainFieldsRegs (BitVec.ofNat 64 (vsaReg afterThird 10).toNat)) fieldsDone
  post : WriteRegistersPost [1, 2] [] fieldsDone jal_80004d94_call.link
    (BitVec.ofNat 64 (vsaReg afterThird 10).toNat) (domainReturnRegs (BitVec.ofNat 64 (vsaReg afterThird 10).toNat)) domainDone

theorem reset_domain_returned_exists : ∃ initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone,
    ResetDomainReturned initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned fieldsDone domainDone := by
  obtain ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, afterThird, afterThirdPublish, returned, w⟩ := reset_tables_return_exists
  obtain ⟨fieldsDone, fieldsRun, fields⟩ := (domain_fields returned _ _ w.fieldsInput).run returned ⟨w.post.pc, rfl⟩
  have leaf : LeafInput jal_8002a934_call.link fieldsDone :=
    ⟨fields.good, fields.image, fields.minstret,
      (fields.frame .x1 (by decide) (by decide)).trans w.fieldsInput.raReg,
      by decide, fields.tick⟩
  have stack : gprGet fieldsDone.σ 2 = some firstMallocStack :=
    (fields.frame .x2 (by decide) (by decide)).trans (show gprGet returned.σ 2 = some firstMallocStack from gholds_lookup _ w.post.regs (by rfl))
  have caller : bytesT fieldsDone.σ.mem domainCallerSlot 8 = jal_80004d94_call.link := by
    rw [fields.memory]
    apply Eq.trans (Vsa.Sim.Boot.bytesT_local_eq (m' := returned.σ.mem) domainCallerSlot 8 ?_) w.caller_word
    intro i hi
    apply frameOn_writeLog _ _ _ domainFields_log_inside
    change (domainCallerSlot + i < firstDomainPtr.toNat ∨ firstDomainPtr.toNat + 928 ≤ domainCallerSlot + i) ∧ True
    have bound : firstDomainPtr.toNat + 928 ≤ domainCallerSlot := by decide
    exact ⟨Or.inr (by omega), trivial⟩
  obtain ⟨domainDone, returnRun, post⟩ := (domain_return fieldsDone _ _ ⟨leaf, stack, fields.result, caller⟩).run fieldsDone ⟨fields.pc, rfl⟩
  exact ⟨initial, atMain, atDomain, atAlloc, atMalloc, afterMalloc, atTables, atRequest, atTableMalloc, afterTable, afterPublish, afterZero, afterThird, afterThirdPublish, returned, fieldsDone, domainDone,
    w, w.run.trans (fieldsRun.trans returnRun), fields, post⟩
end OCaml.Vm.Boot.WhileMinElfParse
