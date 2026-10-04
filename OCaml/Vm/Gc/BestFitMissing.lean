import OCaml.Vm.Gc.BestFitFallback
import OCaml.Vm.Gc.BestFitAccess

namespace OCaml.Vm.Gc.BestFitFallback
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def probeLoads (size : BitVec 64) (c : Config) :=
  [read8 c.σ.mem (BestFitSmall.slot size).toNat]

/-- The concrete small-size slot is empty; the fallback stack geometry is
independent of this read-only classification prefix. -/
structure MissingConditions (R : Nat → BitVec 64) (c : Config) : Prop extends StackConditions R where
  small : (R 10).toNat ≤ Layout.bf_small_count
  slotRead : ReadWindow (BestFitSmall.slot (R 10)) 8
  empty : word c (BestFitSmall.slot (R 10)).toNat = 0

structure MissingInput (R : Nat → BitVec 64) (c : Config) : Prop
    extends Input R c, MissingConditions R c

theorem MissingConditions.of_memory {R before after}
    (memory : after.σ.mem = before.σ.mem) (conditions : MissingConditions R before) :
    MissingConditions R after := by
  refine ⟨conditions.toStackConditions,conditions.small,conditions.slotRead,?_⟩
  simpa only [word,memory] using conditions.empty

theorem probe_access {R c} (input : MissingInput R c) :
    ChainAccess c.σ.mem (BestFitSmall.regs (R 1) (R 10)) (probeLoads (R 10) c) probeBlocks := by
  apply ChainAccess.cons ⟨BestFitSmall.size_access _ _ _ _,BestFitSmall.size_control _ _ _ input.small⟩
  rw [BestFitSmall.size_regs]
  apply ChainAccess.cons (b := probeList) ⟨?_,?_⟩ ChainAccess.nil
  · rw [probe_body]
    exact BestFitSmall.list_access _ _ _ _ [] input.slotRead (read8_pins _ _)
  · change TermFactsO (runGM probeList.body (BestFitSmall.sized (R 1) (R 10))
      [read8 c.σ.mem (BestFitSmall.slot (R 10)).toNat]) probeList.term
    rw [probe_body,BestFitSmall.list_regs]
    simpa [probeList,bf_allocateX73b4FSeg,TermFactsO,TermFactsT,BestFitSmall.listed,
      srcVal,lookupG,guardB,probeLoads,read8_value,word] using input.empty

structure Missing (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost probeBlocks BestFitSmall.pc (BestFitSmall.regs (R 1) (R 10))
    (probeLoads (R 10) before) before after
  pc : PCAt pc after
  registers : GHolds after.σ (regs R)
  memory : after.σ.mem = before.σ.mem

/-- Actual allocator entry classifies a small request and observes its empty
exact-size slot, reaching the bitmap-filtering fallback. -/
theorem missing {R c} (input : MissingInput R c) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Missing R c) := by
  have pins : GHolds c.σ (BestFitSmall.regs (R 1) (R 10)) :=
    ⟨gholds_lookup _ input.registers rfl,gholds_lookup _ input.registers rfl,True.intro⟩
  have summary := block_summary probeBlocks BestFitSmall.pc (BestFitSmall.regs (R 1) (R 10))
    (probeLoads (R 10) c) c
    ⟨input.good,input.minstret,pins,by change KeysOK [1,10]; decide,
      chainPlan_facts (probe_code input.code) (probe_access input),probe_chain,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have pins' := post.regs
  rw [probeLoads,probe_registers] at pins'
  have stack : gprGet after.σ 2 = gprGet c.σ 2 := by
    apply post.frame Register.x2 (by decide)
    intro n hn
    have h := probe_written n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  refine ⟨post,?_,⟨gholds_lookup _ pins' rfl,stack.trans (gholds_lookup _ input.registers rfl),
    gholds_lookup _ pins' rfl,True.intro⟩,?_⟩
  · rw [PCAt,post.pc,probeLoads,probe_endpoint]
  · rw [post.memory,probeLoads,probe_no_stores]
    rfl

/-- Empty exact-size slot and zero filtered bitmap, from real bf_allocate
entry through its decoded ffs call and native return. -/
theorem missing_search_zero {R c} (input : MissingInput R c) (ffsCode : Code.FfsLoaded c.σ.mem)
    (empty : filtered (R 10) (bitmap c) = 0) :
    FnSummary BestFitSmall.pc (fun d => d = c) (Searched R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (missing input).run
  intro middle probed
  have fallback : Input R middle :=
    { toStackConditions := input.toStackConditions
      good := probed.machine.good
      tick := probed.machine.tick
      minstret := probed.machine.minstret
      code := probed.memory ▸ input.code
      registers := probed.registers }
  have same : bitmap middle = bitmap c := by simp only [bitmap,probed.memory]
  obtain ⟨after,run,searched⟩ := (search_zero fallback (probed.memory ▸ ffsCode)
    (same ▸ empty)).run middle ⟨probed.pc,rfl⟩
  refine ⟨after,run,⟨searched.good,searched.tick,searched.minstret,searched.pc,searched.result,
    searched.stack,?_,searched.code,searched.output.trans probed.machine.output,?_⟩⟩
  · rw [searched.memory,probed.memory,same]
  · intro r noise outside
    apply (searched.native r noise outside).trans
    apply probed.machine.frame r noise
    intro n hn
    have h := probe_written n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact outside 12 (by simp)
    · exact outside 13 (by simp)
    · exact outside 14 (by simp)
    · exact outside 15 (by simp)

end OCaml.Vm.Gc.BestFitFallback
