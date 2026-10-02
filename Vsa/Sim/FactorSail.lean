import Lean
import Vsa.Machine
open Lean Meta Elab Command
/-! Factor a deeply nested Sail initializer into small definitionally equal pieces.
This command transforms syntax only: it never executes Sail or supplies an
execution theorem. Each emitted definition and the final reflexivity certificate
are checked by Lean's kernel. Closed bind fragments can then be summarized without
unfolding the complete initializer. The source declaration is unchanged. -/
namespace Vsa.Sim.FactorSail
partial def nodes : Expr → Nat
  | .app f a => 1 + nodes f + nodes a
  | .lam _ t b _ | .forallE _ t b _ => 1 + nodes t + nodes b
  | .letE _ t v b _ => 1 + nodes t + nodes v + nodes b
  | .mdata _ e | .proj _ _ e => 1 + nodes e
  | _ => 1

partial def factor (stem : Name) (e : Expr) : StateT Nat MetaM Expr := do
  let e ← match e with
    | .app f a => pure (.app (← factor stem f) (← factor stem a))
    | .lam n t b k => pure (.lam n t (← factor stem b) k)
    | .letE n t v b k => pure (.letE n t (← factor stem v) (← factor stem b) k)
    | .mdata _ e => factor stem e
    | _ => pure e
  if e.hasLooseBVars || e.hasFVar || e.hasMVar then return e
  if e.getAppFn.constName? != some ``Bind.bind || nodes e < 250 then return e
  let i ← get
  modify (· + 1)
  let name := stem ++ Name.mkSimple s!"chunk{i}"
  let type ← inferType e
  addDecl (.defnDecl { name := name, levelParams := [], type := type, value := e, hints := .abbrev, safety := .safe })
  return mkConst name

elab "#factor_sail " source:ident " as " target:ident : command => do
  let ns ← getCurrNamespace
  liftTermElabM do
    let src ← resolveGlobalConstNoOverload source
    let name := ns ++ target.getId
    let info ← getConstInfoDefn src
    unless info.levelParams.isEmpty do
      throwError "factor_sail expects a monomorphic initializer"
    let (body, count) ← (factor name info.value).run 0
    addDecl (.defnDecl { name := name, levelParams := [], type := info.type, value := body, hints := .abbrev, safety := .safe })
    let lhs := mkConst src
    let rhs := mkConst name
    addDecl (.thmDecl { name := name ++ `eq, levelParams := [], type := ← mkEq lhs rhs, value := ← mkEqRefl lhs })
    logInfo m!"Factored {src}: {count} closed bind fragments"
end Vsa.Sim.FactorSail
