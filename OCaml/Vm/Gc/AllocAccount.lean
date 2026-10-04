import OCaml.Vm.Gc.AllocAccountAccess
import OCaml.Vm.Gc.AllocReturn

namespace OCaml.Vm.Gc.AllocAccount
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def effect (R : Nat → BitVec 64) (c : Config) : List WEntry :=
  headerLog R ++ [(Layout.sym_caml_allocated_words,8,counted R c)]

/-- Memory and arithmetic conditions for the no-major-slice path. -/
structure Conditions (R : Nat → BitVec 64) (c : Config) : Prop where
  headerWrite : WriteWindow (R 10) 8
  thresholdRead : ReadWindow (thresholdAddr R c) 8
  room : (counted R c).toNat ≤ (bytesT (initialized R c) (thresholdAddr R c).toNat 8).toNat

/-- Initial observations select the accounting path that does not request
a major slice. Loads are measured after the explicit header store. -/
structure Input (R : Nat → BitVec 64) (c : Config) : Prop extends Conditions R c where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  registers : GHolds c.σ (regs R)

theorem Conditions.of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem)
    (conditions : Conditions R before) : Conditions R after := by
  constructor
  · exact conditions.headerWrite
  · simpa only [thresholdAddr,state,initialized,memory] using conditions.thresholdRead
  · simpa only [counted,thresholdAddr,state,initialized,memory] using conditions.room

structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs R) (loads R before) before after
  pc : PCAt AllocReturn.pc after
  registers : GHolds after.σ (AllocReturn.regs (R 2) (R 10))
  memory : after.σ.mem = writeLog before.σ.mem (effect R before)
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem

theorem account {R c} (input : Input R c) :
    FnSummary pc (fun d => d = c) (Post R c) := by
  have data : ChainAccess c.σ.mem (regs R) (loads R c) blocks :=
    ChainAccess.cons ⟨access R c input.headerWrite input.thresholdRead,by
      apply control
      simpa only [read8_value,counted] using input.room⟩ ChainAccess.nil
  have facts := chainPlan_facts (code_facts input.code) data
  have summary := block_summary blocks pc (regs R) (loads R c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,8,10,11]; decide,
      facts,chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,image_after Code.caml_alloc_shr_for_minor_gc_transport (by decide) input.code facts post⟩
  · rw [PCAt,post.pc,endpoint]
    rfl
  · have holds := post.regs
    change GHolds after.σ (runGM block.body (regs R) (loads R c)) at holds
    have keep := return_regs R
      (read8 (initialized R c) Layout.sym_caml_allocated_words)
      (read8 (initialized R c) Layout.sym_Caml_state)
      (read8 (initialized R c) (thresholdAddr R c).toNat)
    exact ⟨gholds_lookup _ holds keep.1,gholds_lookup _ holds keep.2,True.intro⟩
  · rw [post.memory]
    change writeLog c.σ.mem (wlogM block.body (regs R) (loads R c)) = _
    rw [loads,writes]
    simp only [effect,headerLog,counted,read8_value,List.cons_append,List.nil_append]

/-- The last accounting store reads back without a separation premise. -/
theorem Post.counter {R before after} (post : Post R before after) :
    word after Layout.sym_caml_allocated_words = counted R before := by
  rw [word,post.memory]
  exact word_writeLog_at _ _ 1 _ _ rfl trivial

end OCaml.Vm.Gc.AllocAccount
