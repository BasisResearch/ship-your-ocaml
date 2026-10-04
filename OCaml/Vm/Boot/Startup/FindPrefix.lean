import OCaml.Vm.Boot.Startup.FindPrefixNormalized
import OCaml.Vm.Boot.Startup.FindPrefixCallInterface
import OCaml.Vm.Boot.Startup.NativeSave
import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.AccessPlan
import Vsa.Sim.ChainFactsTac
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

def findPrefixInput (sp reent name offset ra s1 s2 s3 s5 s6 : BitVec 64) : GRegs :=
  [(2, sp), (19, s3), (9, s1), (18, s2), (21, s5), (22, s6), (1, ra), (11, name), (12, offset), (10, reent)]
def findPrefixLog (sp ra s1 s2 s3 s5 s6 : BitVec 64) : List WEntry :=
  nativeWordLog sp 80 [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra)]

def findPrefixRegs (sp reent name offset ra s1 : BitVec 64) : GRegs :=
  [(21, reent), (22, offset), (18, name), (19, BitVec.ofNat 64 Layout.sym_environ),
   (2, nativeStack sp 80), (9, s1), (1, ra), (11, name), (12, offset), (10, reent)]
def findPrefixBody : List MInstr := (findPrefixSave.headD ⟨[], none⟩).body

local macro "find_prefix_nf" : tactic =>
  `(tactic| simp only [MemFacts, runGM, ldsRunM, wlogM, stepGM, stepLdsM, stepMemM,
    eaddrM, srcVal, lookupG, eraseG, findPrefixInput, wvalM, wentryM, widthOfM,
    List.headD_cons, List.tail_cons, Option.getD_some, Nat.reduceEqDiff, ite_true, ite_false])

theorem findPrefix_body_code {c : Config} (image : ExecutableImage c) : CodeFacts c.σ.mem findPrefixBody := by
  have code := findPrefix_code image
  simp only [findPrefixBody, findPrefixSave, List.headD_cons, CodeFacts]
  chain_facts code with "Vsa.Sim.Code._findenv_r_at_"

theorem findPrefix_access {sp reent name offset ra s1 s2 s3 s5 s6} {c : Config} (frame : NativeFrame sp 80) :
    AccessPlan c.σ.mem (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6) [] findPrefixBody := by
  have window (off : Nat) (bound : off + 8 ≤ 80) (aligned : off % 8 = 0) :
      WriteWindow (nativeStack sp 80 + BitVec.ofNat 64 off) 8 := by
    rw [nativeStack, frame.address off (by omega)]
    exact frame.word bound aligned
  simp only [findPrefixBody, findPrefixSave, List.headD_cons, AccessPlan]
  chain_facts True.intro
  all_goals find_prefix_nf
  · exact ⟨(window 40 (by decide) (by decide)).lower, (window 40 (by decide) (by decide)).upper, (window 40 (by decide) (by decide)).htif, (window 40 (by decide) (by decide)).aligned⟩
  · exact ⟨(window 56 (by decide) (by decide)).lower, (window 56 (by decide) (by decide)).upper, (window 56 (by decide) (by decide)).htif, (window 56 (by decide) (by decide)).aligned⟩
  · exact ⟨(window 48 (by decide) (by decide)).lower, (window 48 (by decide) (by decide)).upper, (window 48 (by decide) (by decide)).htif, (window 48 (by decide) (by decide)).aligned⟩
  · exact ⟨(window 24 (by decide) (by decide)).lower, (window 24 (by decide) (by decide)).upper, (window 24 (by decide) (by decide)).htif, (window 24 (by decide) (by decide)).aligned⟩
  · exact ⟨(window 16 (by decide) (by decide)).lower, (window 16 (by decide) (by decide)).upper, (window 16 (by decide) (by decide)).htif, (window 16 (by decide) (by decide)).aligned⟩
  · exact ⟨(window 72 (by decide) (by decide)).lower, (window 72 (by decide) (by decide)).upper, (window 72 (by decide) (by decide)).htif, (window 72 (by decide) (by decide)).aligned⟩

theorem findPrefix_input {sp reent name offset ra s1 s2 s3 s5 s6 c} (leaf : LeafInput ra c)
    (frame : NativeFrame sp 80) (regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)) :
    BlockInput findenv_rX7438Seg 0x80037438#64 (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6) [] c where
  good := leaf.good
  minstret := leaf.minstret
  regs := regs
  keys := by change KeysOK [2, 19, 9, 18, 21, 22, 1, 11, 12, 10]; decide
  shape := by change ChainOK _ [2, 19, 9, 18, 21, 22, 1, 11, 12, 10] _; decide
  tick := leaf.tick
  facts := by
    rw [← findPrefixSave_eq]
    exact singleton_chain_facts (accessPlan_facts (findPrefix_body_code leaf.image) (findPrefix_access frame)) trivial trivial

theorem findPrefix_bounds {ra s1 s2 s3 s5 s6 : BitVec 64} {off value}
    (member : (off, value) ∈ [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra)]) :
    off + 8 ≤ 80 := by
  change (off, value) ∈ [(40, s3), (56, s1), (48, s2), (24, s5), (16, s6), (72, ra)] at member
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at member
  rcases member with h | h | h | h | h | h | h
  all_goals first | contradiction | (obtain ⟨rfl, _⟩ := h; decide)

theorem findPrefix_log_inside {sp ra s1 s2 s3 s5 s6} (frame : NativeFrame sp 80) :
    LogInW [⟨nativeFrameBase sp 80, sp.toNat⟩] (findPrefixLog sp ra s1 s2 s3 s5 s6) :=
  frame.word_log_inside (fun _ _ member => findPrefix_bounds member)

/-- Save the environment-search caller frame and select the fixed environ global. -/
theorem find_prefix (c : Config) (sp reent name offset ra s1 s2 s3 s5 s6 : BitVec 64)
    (leaf : LeafInput ra c) (frame : NativeFrame sp 80)
    (regs : GHolds c.σ (findPrefixInput sp reent name offset ra s1 s2 s3 s5 s6)) :
    FnSummary 0x80037438#64 (fun d => d = c)
      (WriteRegistersPost [2, 19, 18, 22, 21] (findPrefixLog sp ra s1 s2 s3 s5 s6) c
        jal_80037468_call.pc reent (findPrefixRegs sp reent name offset ra s1)) := by
  apply registers_of_blocks leaf.image (frame.image_outside (findPrefix_log_inside frame)) (block_summary _ _ _ _ _ (findPrefix_input leaf frame regs))
  · rw [← findPrefixSave_eq]
    simp only [findPrefixSave, evalBlocks, evalBlock, SegEvalState.init]
    find_prefix_nf
    rfl
  · rfl
  · rw [← findPrefixSave_eq]
    simp only [findPrefixSave, evalBlocks, evalBlock, SegEvalState.init]
    find_prefix_nf
    simp only [show Functions.sign_extend (m := 64) 0#12 = 0#64 from rfl, BitVec.add_zero]
    rfl
  · rfl
  · decide
end OCaml.Vm.Boot.Startup
