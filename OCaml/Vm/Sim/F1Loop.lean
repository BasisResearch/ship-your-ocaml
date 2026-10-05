import OCaml.RefinementF1
import OCaml.Vm.Sim.Invocation

/-!
# The F1 loop invariant

`F1Loop L P D s c`: the loop-head invariant `LoopAt` (a1-arms,
`OCaml/Refinement.lean`) plus the native invocation `Invocation D` fixed by
entry (`OCaml/Vm/Sim/Invocation.lean`), which STOP and `caml_sys_exit` read
back. It is the `R` of the F1 arm table: `F1Arms P c0 (F1Loop L P D)`, with
`D` the snapshot taken by entry from `c0`.

Build values with `F1Loop.mk'`/`F1Loop.of_plus`, not anonymous
constructors, so fields added to `LoopAt` do not break clients.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- **The F1 loop invariant.** -/
structure F1Loop (L : OCaml.Layout) (P : Prog) (D : InvocationData) (s : St) (c : Config) : Prop where
  loop : OCaml.LoopAt L P s c
  invocation : Invocation D c

theorem F1Loop.mk' {L : OCaml.Layout} {P : Prog} {D : InvocationData} {s : St} {c : Config}
    (loop : OCaml.LoopAt L P s c) (invocation : Invocation D c) : F1Loop L P D s c :=
  ⟨loop, invocation⟩

theorem F1Loop.running {L : OCaml.Layout} {P : Prog} {D : InvocationData} {s : St} {c : Config}
    (h : F1Loop L P D s c) : OCaml.Running L P s c := h.loop.running

/-- An arm's `Running` conclusion plus its preserved invocation re-establish
the F1 invariant (the clock comes from `LoopAt.of_plus`). -/
theorem F1Loop.of_plus {L : OCaml.Layout} {P : Prog} {D : InvocationData} {s s' : St} {c c' : Config}
    (h : F1Loop L P D s c) (run : OCaml.Plus c c') (running : OCaml.Running L P s' c')
    (invocation : Invocation D c') : F1Loop L P D s' c' :=
  ⟨h.loop.of_plus run running, invocation⟩

/-- The common shape of a non-halting F1 row: from the arm's `Running`
conclusion and its footprint-preserved invocation. -/
theorem F1Loop.outcome_of_next {L : OCaml.Layout} {P : Prog} {D : InvocationData} {s : St}
    {c : Config} {r : Res} (h : F1Loop L P D s c)
    (next : ∀ s', r = .next s' → ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P s' c' ∧ Invocation D c')
    (noHalt : ∀ e w, r ≠ .halt e w) : OCaml.ArmOutcome (F1Loop L P D) c r :=
  OCaml.ArmOutcome.of_next (fun s' hr =>
    let ⟨c', run, running, inv⟩ := next s' hr
    ⟨c', run, h.of_plus run running inv⟩) noHalt

end OCaml.Vm.Sim
