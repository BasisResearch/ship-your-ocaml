import OCaml.Vm.Boot.Startup.DomainFields
import OCaml.Vm.Boot.Startup.DomainReturn
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup VsaIris.Inst OCaml.Vm.Primitives
variable {initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned : Config}

theorem ResetTablesReturn.domain_word
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    bytesT returned.σ.mem Layout.sym_Caml_state 8 = firstDomainPtr := by
  have below : ∀ i : Nat, i < 8 → Layout.sym_Caml_state + i < (vsaReg afterThird 10).toNat := by
    have lower := w.third.region.lower
    intro i hi
    unfold Vsa.Sim.DlHeap.heapStart Layout.sym_Caml_state at *
    omega
  rw [w.post.memory, Vsa.Sim.Boot.bytesT_local_eq (m' := afterThirdPublish.σ.mem)
    Layout.sym_Caml_state 8 (fun i hi => memset56Memory_out w.third.region _ _ (Or.inl (below i hi))),
    w.publication.memory, bytesT_writeLog_out _ (show OutLRange (tablePublishLog .customs _) Layout.sym_Caml_state 8 from by
      simp only [tablePublishLog, OutLRange]; decide)]
  exact w.third.publishInput.domainWord

theorem ResetTablesReturn.fieldsInput
    (w : ResetTablesReturn initial atMain atDomain atAlloc atMalloc afterMalloc atTables atRequest atTableMalloc afterTable afterPublish afterZero afterThird afterThirdPublish returned) :
    DomainFieldsInput (BitVec.ofNat 64 (vsaReg afterThird 10).toNat) jal_8002a934_call.link returned where
  toLeafInput := ⟨w.post.good, w.post.image, w.post.minstret, gholds_lookup _ w.post.regs (by rfl), by decide, w.post.tick⟩
  pointer := w.post.result
  domain := w.domain_word
end OCaml.Vm.Boot.WhileMinElfParse
