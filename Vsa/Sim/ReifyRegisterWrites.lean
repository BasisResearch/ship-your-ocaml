import Vsa.Sim.RegisterWrites
import Vsa.Meta.SimpNF

/-! Reify normalized initializer fragments as register-write lists. The reifier
only proposes lists. Each program equality is kernel checked, and execution
comes from the generic `RegisterWrites.run` induction. -/
namespace Vsa.Sim.RegisterWrites
open Lean Meta Elab Command

def assignment (r : LeanRV64DExecutable.Register) (v : LeanRV64DExecutable.RegisterType r) : Assignment := ⟨r, v⟩

private def writeArgs? (e : Expr) : Option (Expr × Expr) := do
  let e := e.consumeMData
  let name ← e.getAppFn.constName?
  if name != ``LeanRV64DExecutable.writeReg && name != ``Sail.ConcurrencyInterfaceV1.PreSail.writeReg then none
  else
    let args := e.getAppArgs
    if args.size < 2 then none else some (args[args.size - 2]!, args[args.size - 1]!)

private partial def reify (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isAppOf ``program then return e.getAppArgs[0]!
  let nil ← mkListLit (mkConst ``Assignment) []
  if let some (r, v) := writeArgs? e then
    return ← mkAppM ``List.cons #[← mkAppM ``assignment #[r, v], nil]
  if e.isAppOfArity ``Bind.bind 6 then
    let args := e.getAppArgs
    let some (r, v) := writeArgs? args[4]! | throwError "initializer contains an action other than writeReg"
    let continuation := args[5]!.consumeMData
    unless continuation.isLambda do throwError "initializer continuation is not a lambda"
    let tail := continuation.bindingBody!
    if tail.hasLooseBVars then throwError "initializer uses a writeReg return value"
    let rest ← reify tail
    return ← mkAppM ``List.cons #[← mkAppM ``assignment #[r, v], rest]
  if e.isAppOf ``Pure.pure && e.getAppArgs.back!.isConstOf ``PUnit.unit then return nil
  throwError "unsupported register initializer expression:{indentExpr e}"

syntax "#reify_register_fragments " ident " as " ident : command

elab_rules : command
  | `(#reify_register_fragments $source:ident as $target:ident) => do
    let ns ← getCurrNamespace
    let src ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo source
    let mut previous : Array (TSyntax `ident) := #[]
    let mut i : Nat := 0
    while (← getEnv).contains (src ++ Name.mkSimple s!"chunk{i}") do
      let old := mkIdent (src ++ Name.mkSimple s!"chunk{i}")
      let nf := mkIdent (target.getId ++ Name.mkSimple s!"normal{i}")
      let entries := ns ++ target.getId ++ Name.mkSimple s!"entries{i}"
      let cert := ns ++ target.getId ++ Name.mkSimple s!"program{i}"
      let args := #[old] ++ previous
      elabCommand (← `(#simp_nf $nf : $old using [$args,*]))
      liftTermElabM do
        let info ← getConstInfoDefn (ns ++ nf.getId)
        let value ← instantiateMVars (← reify info.value)
        unless !value.hasMVar && !value.hasFVar do throwError "register reification left open variables"
        addDecl (.defnDecl { name := entries, levelParams := [], type := ← inferType value, value := value, hints := .abbrev, safety := .safe })
        let rhs ← mkAppM ``program #[mkConst entries]
        let eqType ← mkEq (mkConst old.getId) rhs
        let proof ← mkExpectedTypeHint (mkConst (ns ++ nf.getId ++ `eq)) eqType
        addDecl (.thmDecl { name := cert, levelParams := [], type := eqType, value := proof })
      previous := previous.push (mkIdent cert)
      i := i + 1
    logInfo m!"Reified {i} fragments as checked register-write lists"
end Vsa.Sim.RegisterWrites
