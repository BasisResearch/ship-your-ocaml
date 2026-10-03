import OCaml.Vm.Gc.ChainPlan

namespace OCaml.Vm.Gc
open Vsa.Sim Primitives

/-- Two decoded blocks have the same scalar-access/control obligations and
symbolic data effects. Instruction fetch/decode remains a separate code
certificate, so this permits reuse across different code addresses. -/
structure AccessEquivalent (source target : BBlock) : Prop where
  data : ∀ mem L lds, AccessPlan mem L lds source.body ↔ AccessPlan mem L lds target.body
  control : ∀ L lds, TermFactsO (runGM source.body L lds) source.term ↔
    TermFactsO (runGM target.body L lds) target.term
  log : ∀ L lds, wlogM source.body L lds = wlogM target.body L lds
  registers : ∀ L lds, runGM source.body L lds = runGM target.body L lds
  loads : ∀ lds, ldsRunM source.body lds = ldsRunM target.body lds

/-- Pointwise equivalence of finite reflected block lists. -/
inductive ChainEquivalent : List BBlock → List BBlock → Prop where
  | nil : ChainEquivalent [] []
  | cons {source target sources targets} : AccessEquivalent source target →
      ChainEquivalent sources targets → ChainEquivalent (source :: sources) (target :: targets)

/-- Transport a finite access certificate across reflected equivalent
blocks. This is a certificate fold, not an induction over machine runs. -/
theorem ChainAccess.retarget {mem L lds source target}
    (access : ChainAccess mem L lds source)
    (equivalent : ChainEquivalent source target) :
    ChainAccess mem L lds target := by
  induction access generalizing target with
  | nil => cases equivalent; exact ChainAccess.nil
  | @cons mem L lds b bs head tail ih =>
    cases equivalent with
    | cons same rest =>
      apply ChainAccess.cons ⟨(same.data _ _ _).mp head.data, (same.control _ _).mp head.control⟩
      rw [← same.log, ← same.registers, ← same.loads]
      exact ih rest

end OCaml.Vm.Gc
