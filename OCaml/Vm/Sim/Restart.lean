import OCaml.Vm.Sim.RestartSetupMore
import OCaml.Vm.Sim.RestartSetupEmpty
import OCaml.Vm.Sim.RestartFinish

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- RESTART composes both generated setup paths, the proved arbitrary-count
field copy, and the generated environment-restoration suffix. -/
theorem restart_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a tag : Nat} {fields : List Val} {env : Val}
    (stable : WindowStable L.runtimeOk [⟨restartStart sp fields, sp⟩])
    (h : ArmInput L P s .RESTART c pl cp sp high)
    (block : BlockSelection s.heap pl s.env l a tag fields) (environment : fields[2]? = some env)
    (space : RestartInput P s c pl cp sp high a fields) :
    ∃ after, Plus c after ∧ Running L P (restartState s fields env) after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have setup : ∃ nb after, StepsN nb d after ∧
      RestartCopyStart c sp a (pl.codeBase + 4 * (s.pc + 1)) fields after := by
    by_cases positive : 3 < fields.length
    · exact restart_setup_more h block space positive dp
    · exact restart_setup_empty h block space (by have low := space.lower; omega) dp
  obtain ⟨nf, middle, prefixSteps, front⟩ := setup
  obtain ⟨copied, copySteps, back⟩ := forward_copy_run (space.copy_after block front) middle front.copy
  obtain ⟨nb, after, suffixSteps, running⟩ := restart_finish stable h block environment space front back
  have frontRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp prefixSteps⟩
  have backRun : Steps copied after := OCaml.Run.vsa_steps_iff.mpr ⟨nb, OCaml.Run.vsa_stepsN_iff.mp suffixSteps⟩
  obtain ⟨n, whole⟩ := (frontRun.trans (copySteps.trans backRun)).toN
  exact ⟨n, after, whole, running⟩

/-- The successful bytecode rule selects the same restored partial-closure state. -/
theorem restart_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a tag : Nat} {fields : List Val} {env : Val}
    (stable : WindowStable L.runtimeOk [⟨restartStart sp fields, sp⟩])
    (h : ArmInput L P s .RESTART c pl cp sp high)
    (block : BlockSelection s.heap pl s.env l a tag fields) (environment : fields[2]? = some env)
    (space : RestartInput P s c pl cp sp high a fields)
    (step : stepI P s ⟨.RESTART, []⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have valid : ¬ fields.length < 3 := by have low := space.lower; omega
  have selected : fields.getD 2 .unit = env := by
    simp only [List.getD_eq_getElem?_getD, environment, Option.getD_some]
  have state : restartState s fields env = s' := by
    simpa only [stepI, block.pointer, block.object, valid, ite_false, selected,
      St.adv, restartState, Res.next.injEq] using step
  rw [← state]
  exact restart_arm stable h block environment space

end OCaml.Vm.Sim
