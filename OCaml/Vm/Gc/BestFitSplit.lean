import OCaml.Vm.Gc.BestFitSplitAccess

namespace OCaml.Vm.Gc.BestFitSplit
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def header (source : BitVec 64) (c : Config) := word c (headerAddr source).toNat
def loads (source : BitVec 64) (c : Config) :=
  [read8 c.σ.mem (headerAddr source).toNat,read8 c.σ.mem Layout.sym_caml_fl_cur_wsz]
def effect (request source : BitVec 64) (c : Config) : List WEntry :=
  [(Layout.sym_caml_fl_cur_wsz,8,word c Layout.sym_caml_fl_cur_wsz - 1#64 - sizeWord (header source c)),
   ((headerAddr source).toNat,8,remnantHeader (route request (header source c)) (delta request (header source c)))]

/-- Machine preconditions for splitting an existing major-heap free block.
The caller supplies ownership separately when composing this exact run. -/
structure Input (ra request source : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Bf_splitLoaded c.σ.mem
  registers : GHolds c.σ (regs ra request source)
  headerWrite : WriteWindow (headerAddr source) 8
  aligned : ra.toNat % 4 = 0

theorem access {ra request source c} (input : Input ra request source c) :
    ChainAccess c.σ.mem (regs ra request source) (loads source c)
      (blocks (route request (header source c))) := by
  unfold blocks
  simp only [List.cons_append,List.nil_append]
  apply ChainAccess.cons ⟨head_access _ _ _ _ _ _ _ input.headerWrite.read (read8_pins _ _) (read8_pins _ _),?_⟩
  · simp only [loads,head_regs,head_loads,head_log]
    generalize he : route request (header source c) = large
    cases large
    · simp only [Bool.false_eq_true,ite_false,List.cons_append,List.nil_append]
      apply ChainAccess.cons ⟨small_access _ _ _ _ _,True.intro⟩
      rw [small_regs,small_loads,small_log]
      apply ChainAccess.cons (b := returnBlock) ⟨?_,?_⟩ ChainAccess.nil
      · exact return_access false _ _ _ _ _ input.headerWrite
      · exact return_control false _ _ _ _ input.aligned
    · simp only [ite_true,List.nil_append]
      apply ChainAccess.cons (b := returnBlock) ⟨?_,?_⟩ ChainAccess.nil
      · exact return_access true _ _ _ _ _ input.headerWrite
      · exact return_control true _ _ _ _ input.aligned
  · simpa only [loads,header,word,read8_value] using head_control ra request source
      (read8 c.σ.mem (headerAddr source).toNat) (read8 c.σ.mem Layout.sym_caml_fl_cur_wsz)

/-- Both native paths return the carved header address and perform exactly
one free-word accounting store and one remnant-header store. -/
structure Post (ra request source : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost (blocks (route request (header source before))) pc
    (regs ra request source) (loads source before) before after
  pc : PCAt ra after
  result : gprGet after.σ 10 = some ((delta request (header source before) <<< (3 : Nat)) + headerAddr source)
  memory : after.σ.mem = writeLog before.σ.mem (effect request source before)
  code : Code.Bf_splitLoaded after.σ.mem

theorem split {ra request source c} (input : Input ra request source c) :
    FnSummary pc (fun d => d = c) (Post ra request source c) := by
  have facts := chainPlan_facts (code_facts _ input.code) (access input)
  have summary := block_summary (blocks (route request (header source c))) pc
    (regs ra request source) (loads source c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [1,10,11]; decide,
      facts,chain_ok _,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.bf_split_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,loads,endpoint _ _ _ _ _ _ input.aligned]
  · have regsPost := post.regs
    rw [loads,BestFitSplit.registers] at regsPost
    have result := gholds_lookup _ regsPost (return_value _ _ _ _ _)
    simpa only [read8_value,header,word] using result
  · rw [post.memory,loads,writes]
    simp only [effect,read8_value,header,word]

end OCaml.Vm.Gc.BestFitSplit
