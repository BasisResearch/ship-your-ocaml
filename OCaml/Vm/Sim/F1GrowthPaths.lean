import OCaml.Vm.Sim.F1Growth

/-!
# The remembered set's growth paths for F1

`f1_barrierGrowth_dense` (a6-gc) runs the growing barrier at a call state
that is RAM-dense and has every integer register present. Those two facts
at `caml_modify`'s entry are the named premise `GrowthCallState`; with it the
unallocated table's growth path is discharged, and the F1 table's
layout-level premise is `F1GrowthPremises`: the call state and the full
table's realloc branch.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **The call state at `caml_modify`'s entry** (named premise; supplied by the
loop invariant once RAM density, the foreman's route (B)/(C), and
`LoopRegisters.gprs`, a1-arms, are carried): every RAM byte present and every
integer register present. -/
structure GrowthCallState (L : OCaml.Layout) : Prop where
  dense : ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (sp high codeReg : Nat)
    (ra codeWord stackWord slot value : BitVec 64) (c : Config),
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value c →
    ∀ x, Boot.Startup.startupLive x → (c.σ.mem[x]?).isSome
  gprs : ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (sp high codeReg : Nat)
    (ra codeWord stackWord slot value : BitVec 64) (c : Config),
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value c →
    Boot.Startup.GprPresent c.σ

/-- **The unallocated remembered set's growth path for F1**, over a6-gc's
`f1_barrierGrowth_dense`. -/
theorem f1_barrierGrowth (st : GrowthCallState Gc.f1Layout) : BarrierGrowth Gc.f1Layout where
  grow P s pl cp sp high codeReg ra codeWord stackWord value c l a i tag fields vVal D tbl ptr limit
      input inv v low live placed selected bound represented root fieldStable table emptyW grows :=
    f1_barrierGrowth_dense input inv v low live placed selected bound represented root fieldStable
      table emptyW grows (st.dense _ _ _ _ _ _ _ _ _ _ _ _ _ input) (st.gprs _ _ _ _ _ _ _ _ _ _ _ _ _ input)

/-- **The F1 table's layout-level premises**: the call state at `caml_modify`'s
entry and the full table's realloc branch (GC lane). -/
structure F1GrowthPremises : Prop where
  callState : GrowthCallState Gc.f1Layout
  full : BarrierGrowthFull Gc.f1Layout

theorem F1GrowthPremises.paths (h : F1GrowthPremises) : BarrierGrowthPaths Gc.f1Layout :=
  ⟨f1_barrierGrowth h.callState, h.full⟩

end OCaml.Vm.Sim
