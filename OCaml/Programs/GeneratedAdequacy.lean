import OCaml.Programs.Generated.Demo
import OCaml.Logic.BcModel
import VsaIris.MachWP

/-! End-to-end Iris instantiation of a generated branch-function summary. -/
namespace OCaml.Programs.GeneratedAdequacy
open OCaml.Bytecode OCaml.Logic OCaml.Programs.Generated.Demo
open VsaIris Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

/-- The generated summary changes only the PC; all memory and console
ownership is framed by the existing MachWP segment interface. -/
theorem jump_runFact : RunFact (bcModel jumpStop) 0 [] [] [(0, 0, 2)] [] := by
  intro s hok hf
  have hr := hf.2.2.1 (0, 0, 2) (by simp)
  have hp := pc_eq_of_reg hok (pc := 0) (by decide) hr
  rcases s with ⟨pc, a, rest, e, x, t, h, w⟩
  dsimp at hp
  subst pc
  refine ⟨⟨2, a, rest, e, x, t, h, w⟩,
    reachesN_of_symbolic (jumpStop_summary a e rest x t h w), by exact ⟨by change 2 < 2^64; decide, hok.extra⟩, ?_, rfl⟩
  constructor
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    rfl
  · intro k hk
    cases k with
    | zero => exact False.elim (hk (0, 0, 2) (by simp) rfl)
    | succ k => simp only [bcModel]; split <;> first | rfl | omega
  · intro p hp; cases hp
  · intro k _; rfl

/-- The terminal instruction is STOP at the summary's return PC. -/
theorem jump_haltFact : HaltFact (bcModel jumpStop) [(0, DFrac.own 1, 2)] [] 0 := by
  intro s hok hf
  have hr := hf.1 (0, DFrac.own 1, 2) (by simp)
  have hp := pc_eq_of_reg hok (pc := 2) (by decide) hr
  have hs : step jumpStop s = .halt 0 s.world := by
    unfold step
    rw [hp]
    rfl
  simp only [bcModel, hs]

/-- WP of the generated function, uniformly for total and partial MachWP. -/
theorem jump_wp {GF : BundledGFunctors} [MachGS .hasLC GF]
    (Wp : MachWP (GF := GF) (bcModel jumpStop)) (out : String) :
    (0 ↦ᵣ (0#64)) ∗ consoleOwn out ⊢ Wp.W (fun v => iprop(⌜v = (0, out)⌝)) := by
  iintro ⟨Hpc, Hout⟩
  iapply Wp.run 0 [] [] [(0, 0, 2)] [] jump_runFact
  isplitl [Hpc]
  · simp only [footPre, sepL_cons, sepL_nil]
    iframe Hpc
  simp only [footPost, sepL_cons, sepL_nil]
  iintro ⟨_, _, ⟨Hpc, _⟩, _⟩
  iapply Wp.haltConsole [(0, DFrac.own 1, 2)] [] 0 out jump_haltFact
  simp only [footPre, sepL_cons, sepL_nil]
  iframe Hpc Hout
  ipureintro; simp

/-- Initial ownership supplies the WP hypothesis; no semantic assumption is
left to the client of `jumpStop_adequacy`. -/
theorem jump_hyp : AdequacyHyp MachGF (bcModel jumpStop)
    (PartialMap.singleton 0 (0#64)) ∅ "" (fun v => v = (0, "")) := by
  intro G
  simp only [BigSepM.bigSepM_singleton.to_eq, BigSepM.bigSepM_empty.to_eq]
  iintro Hpc _ Hout
  have hw := jump_wp (twpW (GF := MachGF) (bcModel jumpStop)) ""
  simp only [twpW_W] at hw
  iapply hw
  iframe Hpc Hout

/-- `bytecode_adequacy` instantiated with a generated function summary,
MachWP rules, and proved initial register/memory ownership. -/
theorem jumpStop_adequacy : BcHalts jumpStop "" 0 := by
  have hr : RegAgree (bcModel jumpStop) (PartialMap.singleton 0 (0#64)) jumpStop.init := by
    intro k v hv
    simp only [LawfulPartialMap.get?_singleton] at hv
    split at hv
    · rename_i he
      subst k
      cases hv
      rfl
    · cases hv
  have hm : MemAgree (bcModel jumpStop) ∅ jumpStop.init := by
    intro k v hv
    rw [LawfulPartialMap.get?_empty] at hv
    cases hv
  obtain ⟨e, out, hh, he⟩ := bytecode_adequacy (GF := MachGF) jumpStop
    (PartialMap.singleton 0 (0#64)) ∅ hr hm (fun v => v = (0, "")) jump_hyp
  cases he
  exact hh

end OCaml.Programs.GeneratedAdequacy
