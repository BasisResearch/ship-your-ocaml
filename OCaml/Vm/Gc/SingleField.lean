import OCaml.Vm.Gc.Generated.SingleField
import OCaml.Vm.Gc.EnqueueAccess
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A size-one scanned object takes the non-queue branch after the same
three forwarding stores. The source load observes the preceding root store. -/
structure Input (q : PendingCopy) (root : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (Enqueue.regs q.source q.target root 1)
  windows : WorkQueue.PrefixWindows q root

theorem access {q root c} (input : Input q root c) :
    ChainAccess c.σ.mem (Enqueue.regs q.source q.target root 1)
      (WorkQueue.enqueueLoads q root c) blocks := by
  rw [blocks_eq]
  apply ChainAccess.cons ⟨?_,?_⟩ ChainAccess.nil
  · rw [body_eq]
    exact WorkQueue.enqueue_prefix_access q root 1 c input.windows
  · rw [body_eq,Enqueue.prefix_regs]
    simp [block,blocks,caml_oldify_oneX9ba4FSeg,TermFactsO,TermFactsT,
      Enqueue.afterPrefixRegs,srcVal,lookupG,guardB,Functions.zopz0zI_u]

structure Post (q : PendingCopy) (root : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (Enqueue.regs q.source q.target root 1)
    (WorkQueue.enqueueLoads q root before) before after
  pc : PCAt exitPc after
  registers : GHolds after.σ (Enqueue.afterPrefixRegs q.source q.target 1
    (bytesVal .ld ((WorkQueue.enqueueLoads q root before).headD [])))
  memory : after.σ.mem = writeLog before.σ.mem (Enqueue.prefixLog q.source q.target root)
  code : Code.Caml_oldify_oneLoaded after.σ.mem

/-- Actual single-field forwarding prefix to the child's tagged-value test.
The child tail route and original native return follow separately. -/
theorem prepare {q root c} (input : Input q root c) :
    FnSummary pc (fun d => d = c) (Post q root c) := by
  have summary := block_summary blocks pc (Enqueue.regs q.source q.target root 1)
    (WorkQueue.enqueueLoads q root c) c
    ⟨input.good,input.minstret,input.registers,by change KeysOK [10,9,8,24,22,25]; decide,
      chainPlan_facts (code_facts input.code) (access input),chain_ok,input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post,?_,?_,?_,?_⟩
  · rw [PCAt,post.pc,endpoint]
  · simpa only [registers] using post.regs
  · rw [post.memory,writes]
  · exact image_after Code.caml_oldify_one_transport (by decide) input.code
      (chainPlan_facts (code_facts input.code) (access input)) post

end OCaml.Vm.Gc.SingleField
