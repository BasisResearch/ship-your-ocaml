import VsaIris.Vsa.ProofPieces

namespace VsaIris.Sym
open Lean Elab Command Term Meta

/-- Close every continuation of a checked piece with a separately checked branch.
The branches have the original parameters followed by the continuation's locals. -/
syntax (name := ixFork) "#ix_fork " ident " := " ident " [" ident,+ "]" : command

@[command_elab ixFork] def elabIxFork : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let first ← liftCoreM <| realizeGlobalConstNoOverload stx[3]
  let branches ← stx[5].getSepArgs.mapM fun n => liftCoreM <| realizeGlobalConstNoOverload n
  liftTermElabM do
    let info ← getConstInfo first
    forallTelescope info.type fun xs goal => do
      let nv ← pieceVars xs
      let vars := xs.extract 0 nv
      let continuations := xs.extract nv xs.size
      unless branches.size == continuations.size do
        throwError "#ix_fork: expected {continuations.size} branches, got {branches.size}"
      let mut args := #[]
      for i in [:branches.size] do
        let value ← forallTelescope (← inferType continuations[i]!) fun ys target => do
          let value := mkAppN (Lean.mkConst branches[i]!) (vars ++ ys)
          unless ← isDefEq (← inferType value) target do
            throwError "#ix_fork: branch {branches[i]!} does not close its continuation"
          mkLambdaFVars ys value
        args := args.push value
      let value ← instantiateMVars (← mkLambdaFVars vars (mkAppN (Lean.mkConst first) (vars ++ args)))
      let type ← instantiateMVars (← mkForallFVars vars goal)
      if value.hasMVar || value.hasFVar || type.hasMVar || type.hasFVar then
        throwError "#ix_fork: unresolved variables"
      addDecl (.thmDecl {name := declName, levelParams := [], type, value})

end VsaIris.Sym
