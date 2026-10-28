import OCaml.Vm.Sim.F1Growth

/-!
# The remembered set's growth paths for F1

`f1_barrierGrowth_gprs` (a6-gc) runs the growing barrier at a call state
with every integer register present. That fact at `caml_modify`'s entry is
the named premise `GrowthCallState`; with it the
unallocated table's growth path is discharged, and the F1 table's
layout-level premise is `F1GrowthPremises`: the call state and the full
table's realloc branch.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- **The call state at `caml_modify`'s entry** (named premise; supplied by the
loop invariant once `LoopRegisters.gprs`, a1-arms, is carried): every integer
register present. -/
structure GrowthCallState (L : OCaml.Layout) : Prop where
  gprs : ∀ (P : Prog) (s : St) (pl : Place) (cp : ChanPlace) (sp high codeReg : Nat)
    (ra codeWord stackWord slot value : BitVec 64) (c : Config),
    ModifyInput L P s pl cp sp high codeReg ra codeWord stackWord slot value c →
    Boot.Startup.GprPresent c.σ

/-- **GPR presence at `caml_modify`'s entry**: the barrier call's input carries
the loop registers, which carry complete GPR presence. -/
theorem growthCallState (L : OCaml.Layout) : GrowthCallState L :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ input => input.loop.gprs⟩

/-- Compose the existing native path once at a layout whose budget and
runtime project to F1. All extra runtime observations come from its actual
GrowDone frame, and every native post field is retained. -/
theorem barrierGrowth_of_runtime {L : OCaml.Layout}
    (budget : L.budget = Gc.f1Layout.budget)
    (project : ∀ c, L.runtimeOk c → Gc.f1Runtime c)
    (idle : ∀ c, L.runtimeOk c → bytesT c.σ.mem Layout.sym_caml_gc_phase 4 = 3#32)
    (runtime : BarrierGrowRuntime L) : BarrierGrowth L where
  grow P s pl cp sp high codeReg ra codeWord stackWord value c l a i tag fields vVal D tbl ptr limit
      input inv valid low live placed selected bound represented root fieldStable table empty grows :=
    barrierGrowth_gprs_of_runtime budget project idle runtime input inv valid low live placed selected
      bound represented root fieldStable table empty grows input.loop.gprs

/-- **The unallocated remembered set's growth path for F1**, over a6-gc's
`f1_barrierGrowth_gprs`. -/
theorem f1_barrierGrowth (st : GrowthCallState Gc.f1Layout) : BarrierGrowth Gc.f1Layout where
  grow P s pl cp sp high codeReg ra codeWord stackWord value c l a i tag fields vVal D tbl ptr limit
      input inv v low live placed selected bound represented root fieldStable table emptyW grows :=
    f1_barrierGrowth_gprs input inv v low live placed selected bound represented root fieldStable
      table emptyW grows (st.gprs _ _ _ _ _ _ _ _ _ _ _ _ _ input)

/-- **The F1 table's layout-level premises**: the call state at `caml_modify`'s
entry is `growthCallState`; the full table's realloc branch (GC lane). -/
structure F1GrowthPremises : Prop where
  full : BarrierGrowthFull Gc.f1Layout

theorem F1GrowthPremises.paths (h : F1GrowthPremises) : BarrierGrowthPaths Gc.f1Layout :=
  ⟨f1_barrierGrowth (growthCallState _), h.full⟩

end OCaml.Vm.Sim
