import Vsa.Sim.FactorSail
import Vsa.Meta.SimpNF

/-! Normalize a factored initializer a fragment at a time with `#simp_nf`.
Each fragment uses the preceding fragments' checked equalities, keeping their
normal forms folded. This performs symbolic rewriting, not machine execution. -/
namespace Vsa.Sim.NormalizeSail
open Lean Elab Command

syntax "#normalize_sail " ident " as " ident bracketedBinder* " : " term " using " "[" ident,* "]" : command

elab_rules : command
  | `(#normalize_sail $source:ident as $target:ident $bs:bracketedBinder* : $body:term using [$rules,*]) => do
    let src ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo source
    let mut previous : Array (TSyntax `ident) := #[]
    let mut i : Nat := 0
    while (← getEnv).contains (src ++ Name.mkSimple s!"chunk{i}") do
      let old := mkIdent (src ++ Name.mkSimple s!"chunk{i}")
      let fresh := mkIdent (target.getId ++ Name.mkSimple s!"chunk{i}")
      let args := #[old] ++ rules.getElems ++ previous
      elabCommand (← `(#simp_nf $fresh : $old using [$args,*]))
      previous := previous.push (mkIdent (fresh.getId ++ `eq))
      i := i + 1
    let args := #[source] ++ rules.getElems ++ previous
    elabCommand (← `(#simp_nf $target $bs* : $body using [$args,*]))
    logInfo m!"Normalized {src}: {i} fragments, each with a simp certificate"

end Vsa.Sim.NormalizeSail
