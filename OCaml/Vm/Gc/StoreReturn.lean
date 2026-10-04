import OCaml.Vm.Gc.Generated.StoreReturn
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.StoreReturn
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Native-stack and destination geometry for oldify's store/return path.
The final value store must preserve the three subsequent native loads. -/
structure Windows (sp value target : BitVec 64) : Prop where
  stack : ∀ off ∈ offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8
  destination : WriteWindow target 8
  outside : ∀ cell ∈ returnSlots, OutLRange (effect value target) (sp + BitVec.ofNat 64 cell.2).toNat 8

structure Input (sp value target : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs sp value target)
  windows : Windows sp value target
  aligned : (returnWord sp c).toNat % 4 = 0

theorem access {sp value target c} (input : Input sp value target c) :
    ChainAccess c.σ.mem (regs sp value target) (loads sp c) blocks := by
  apply ChainAccess.cons ⟨pre_access sp value target c input.windows.stack,True.intro⟩
  rw [pre_regs,pre_loads,pre_log]
  exact ChainAccess.cons ⟨return_access sp value target c input.windows.stack input.windows.destination
    input.windows.outside,control sp value target c input.aligned⟩ ChainAccess.nil

structure Post (sp value target : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs sp value target) (loads sp before) before after
  pc : PCAt (returnWord sp before) after
  registers : GHolds after.σ (restored sp before)
  memory : after.σ.mem = writeLog before.σ.mem (effect value target)
  value : word after target.toNat = value
  code : Code.Caml_oldify_oneLoaded after.σ.mem

/-- Actual native restore, final destination store and return. Stack values
remain observations, ready for identification by the common saved-bank proof. -/
theorem finish {sp value target c} (input : Input sp value target c) :
    FnSummary pc (fun d => d = c) (Post sp value target c) := by
  have summary := block_summary blocks pc (regs sp value target) (loads sp c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [2,8,9]; decide,
      chainPlan_facts (code_facts input.code) (access input),chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = writeLog c.σ.mem (effect value target) := by rw [post.memory,writes]
  refine ⟨post,?_,?_,memory,?_,?_⟩
  · rw [PCAt,post.pc,endpoint sp value target c input.aligned]
  · simpa only [registers] using post.regs
  · rw [word,memory]
    exact word_writeLog_at _ _ 0 _ _ rfl True.intro
  · exact image_after Code.caml_oldify_one_transport (by decide) input.code
      (chainPlan_facts (code_facts input.code) (access input)) post

end OCaml.Vm.Gc.StoreReturn
