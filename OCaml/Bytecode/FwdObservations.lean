import OCaml.Bytecode.GcSafe
import OCaml.Run.Observe

namespace OCaml.Bytecode

/-- Different-length finite prefixes reaching the same continuation have the
same Layer A observations. Used for the two already-forced Lazy.force paths. -/
theorem FwdObservations.of_common_result {P : Prog} {s t u : St} {n m : Nat}
    (left : Run.iter (bcK P) n s = .ok u)
    (right : Run.iter (bcK P) m t = .ok u) : FwdObservations P s t where
  halt := fun out e => exists_congr fun w => and_congr
    ((Run.halts_after_iter left (.halt e w)).trans (Run.halts_after_iter right (.halt e w)).symm)
    Iff.rfl
  diverge := (Run.div_after_iter left).trans (Run.div_after_iter right).symm

/-- Observational equivalence composes without a lockstep requirement. -/
theorem FwdObservations.trans {P : Prog} {s t u : St}
    (left : FwdObservations P s t) (right : FwdObservations P t u) :
    FwdObservations P s u where
  halt := fun out e => (left.halt out e).trans (right.halt out e)
  diverge := left.diverge.trans right.diverge

end OCaml.Bytecode
