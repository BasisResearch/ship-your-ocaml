import OCaml.Programs.Generated.IntAbs
import OCaml.Logic.BcModel
import VsaIris.MachWP

namespace OCaml.Programs.CompilerFunctionAdequacy
open OCaml.Bytecode OCaml.Logic OCaml.Programs.Generated.IntAbs
open VsaIris Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

/-- The proved compiler function returns seven on negative seven. The frame
retains the caller's heap, stack, environment, trap and console. -/
theorem abs_runFact : RunFact (bcModel absHarness) 8 [(4, DFrac.own 1, 0)] []
    [(0, 0, 7), (1, 1, 15)] [] := by
  intro s hok hf
  rcases hf with ⟨readRegs, _, writeRegs, _⟩
  have hp := pc_eq_of_reg hok (pc := 0) (by decide)
    (writeRegs (0, 0, 7) (by simp))
  have hx := extra_zero_of_reg hok (readRegs (4, DFrac.own 1, 0) (by simp))
  rcases s with ⟨pc, a, rest, env, extra, trap, heap, world⟩
  dsimp at hp hx
  subst pc
  subst extra
  refine ⟨⟨7, Val.ofInt 7, rest, env, 0, trap, heap, world⟩,
    reachesN_of_symbolic (harness_run a env rest trap heap world),
    ⟨by change 7 < 2^64; decide, by change 0 < 2^63; decide⟩, ?_, rfl⟩
  constructor
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro k hk
    have h0 : k ≠ 0 := fun h => hk (0, 0, 7) (by simp) (by simpa using h.symm)
    have h1 : k ≠ 1 := fun h => hk (1, 1, 15) (by simp) (by simpa using h.symm)
    simp only [bcModel]
    split <;> first | rfl | omega
  · intro p hp; cases hp
  · intro k _; rfl

/-- STOP is reached only after the actual helper has returned its result. -/
theorem abs_haltFact : HaltFact (bcModel absHarness) [(0, DFrac.own 1, 7)] [] 0 := by
  intro s hok hf
  have hp := pc_eq_of_reg hok (pc := 7) (by decide) (hf.1 (0, DFrac.own 1, 7) (by simp))
  have hs : step absHarness s = .halt 0 s.world := by
    unfold step
    rw [hp]
    rfl
  simp only [bcModel, hs]

/-- The actual compiler helper's generated functional summary supplies the
run rule, uniformly for partial and total WP. -/
theorem abs_wp {GF : BundledGFunctors} [MachGS .hasLC GF]
    (Wp : MachWP (GF := GF) (bcModel absHarness)) (out : String) :
    (0 ↦ᵣ (0#64)) ∗ (1 ↦ᵣ (1#64)) ∗ (4 ↦ᵣ (0#64)) ∗ consoleOwn out ⊢
      Wp.W (fun v => iprop(⌜v = (0, out)⌝)) := by
  iintro ⟨Hpc, Ha, Hextra, Hout⟩
  iapply Wp.run 8 [(4, DFrac.own 1, 0)] [] [(0, 0, 7), (1, 1, 15)] [] abs_runFact
  isplitl [Hpc Ha Hextra]
  · simp only [footPre, sepL_cons, sepL_nil]
    iframe Hpc Ha Hextra
  simp only [footPost, sepL_cons, sepL_nil]
  iintro ⟨_, _, ⟨Hpc, _, _⟩, _⟩
  iapply Wp.haltConsole [(0, DFrac.own 1, 7)] [] 0 out abs_haltFact
  simp only [footPre, sepL_cons, sepL_nil]
  iframe Hpc Hout
  ipureintro; simp

/-- Initial ownership needed for the three-register footprint. -/
def absRegs : NatMap (BitVec 64) :=
  PartialMap.insert (PartialMap.insert (PartialMap.singleton 0 0) 1 1) 4 0

theorem abs_hyp : AdequacyHyp MachGF (bcModel absHarness) absRegs ∅ "" (fun v => v = (0, "")) := by
  intro G
  have h1 : PartialMap.get? (PartialMap.singleton 0 (0#64) : NatMap (BitVec 64)) 1 = none := by
    simp [LawfulPartialMap.get?_singleton]
  have h4 : PartialMap.get? (PartialMap.insert (PartialMap.singleton 0 (0#64) : NatMap (BitVec 64)) 1 1) 4 = none := by
    simp [LawfulPartialMap.get?_insert, LawfulPartialMap.get?_singleton]
  simp only [absRegs]
  iintro Hr _ Hout
  ihave Hr4 := (BigSepM.bigSepM_insert h4).1 $$ Hr
  icases Hr4 with ⟨Hextra, Hr1⟩
  ihave Hr1' := (BigSepM.bigSepM_insert h1).1 $$ Hr1
  icases Hr1' with ⟨Ha, Hr0⟩
  ihave Hpc := BigSepM.bigSepM_singleton.1 $$ Hr0
  have hw := abs_wp (twpW (GF := MachGF) (bcModel absHarness)) ""
  simp only [twpW_W] at hw
  iapply hw
  iframe Hpc Ha Hextra Hout

/-- End-to-end adequacy of a harness invoking unchanged compiler Int.abs
bytes on -7. `harness_run` also proves the functional result is seven;
this theorem discharges termination through `bytecode_adequacy`. -/
theorem compiler_abs_adequacy : BcHalts absHarness "" 0 := by
  have hr : RegAgree (bcModel absHarness) absRegs absHarness.init := by
    intro k v hv
    simp only [absRegs, LawfulPartialMap.get?_insert, LawfulPartialMap.get?_singleton] at hv
    split at hv
    · rename_i eq; subst k; cases hv; rfl
    · split at hv
      · rename_i eq; subst k; cases hv; rfl
      · split at hv
        · rename_i eq; subst k; cases hv; rfl
        · cases hv
  have hm : MemAgree (bcModel absHarness) ∅ absHarness.init := by
    intro k v hv
    rw [LawfulPartialMap.get?_empty] at hv
    cases hv
  obtain ⟨e, out, halt, post⟩ := bytecode_adequacy (GF := MachGF) absHarness
    absRegs ∅ hr hm (fun v => v = (0, "")) abs_hyp
  cases post
  exact halt

end OCaml.Programs.CompilerFunctionAdequacy
