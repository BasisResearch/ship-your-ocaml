import OCaml.Refinement
import OCaml.Bytecode.FwdObservations

/-! The observational GC boundary. Strict relocation remains the Eqv route for
ordinary objects; a Forward shortcut may change the represented BcSem state.
GcSafe connects that actual state to the original deterministic continuation. -/
namespace OCaml.Vm.Gc
open OCaml.Bytecode Vsa.Machine

/-- A machine boundary representing an actual, possibly shortened heap while
retaining the observations of the original deterministic continuation. R is
the caller-supplied root/continuation representation at this boundary. -/
structure ObservedAt (P : Prog) (R : St → Config → Prop) (original actual : St)
    (c : Config) : Prop where
  reached : GcReach P actual
  represented : R actual c
  observations : FwdObservations P original actual

/-- The concrete oldify/mopup composition must supply this effect. This is a
named open obligation, not a machine execution theorem. Frame/placement facts
for unchanged objects use Eqv; roots and shortcut fields establish a directed FwdReduction (hence FwdEq). -/
structure CollectionEffect (P : Prog) (R : St → Config → Prop) (before after : St)
    (c c' : Config) : Prop where
  run : Plus c c'
  shortcuts : FwdReduction before after
  represented : R after c'

/-- A proved machine effect and GcSafe preserve the original observations.
This is the boundary composition rule, not a proof of the effect's premises. -/
theorem ObservedAt.collect {P R R' original before after c c'}
    (safe : GcSafe P) (head : ObservedAt P R original before c)
    (point : CollectionPoint P before)
    (effect : CollectionEffect P R' before after c c') :
    Plus c c' ∧ ObservedAt P R' original after c' :=
  ⟨effect.run, .collect head.reached point effect.shortcuts, effect.represented,
    head.observations.trans (safe before after head.reached point effect.shortcuts)⟩

end OCaml.Vm.Gc
