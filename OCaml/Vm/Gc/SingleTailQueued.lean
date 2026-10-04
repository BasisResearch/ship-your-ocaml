import OCaml.Vm.Gc.QueuedChildTable
import OCaml.Vm.Gc.SingleTailState

namespace OCaml.Vm.Gc.SingleTail
open Vsa.Machine Vsa.Sim Primitives

/-- Finite separation supplied by heap ownership at a queued-child exit.
Both newly forwarded sources are exempt from unchanged-header footprints;
all previously published forwarding words remain protected. -/
structure QueuedExitFootprint (q : PendingCopy) (root payload : BitVec 64)
    (log : List WEntry) (qs copies : List PendingCopy) (sources : List (BitVec 64)) (c : Config) : Prop where
  parentOutside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root)
  suffixOutside : ForwardingTable.Outside (q :: copies)
    (log ++ Fresh.contextQueueEffect (SingleField.child q root c) payload q.target
      (Enqueue.prefixLog q.source q.target root ++ log) qs c)
  otherHeaders : ∀ source ∈ sources, source ≠ q.source → source ≠ SingleField.child q root c →
    OutLRange ((Enqueue.prefixLog q.source q.target root ++ log) ++
      Fresh.contextQueueEffect (SingleField.child q root c) payload q.target
        (Enqueue.prefixLog q.source q.target root ++ log) qs c) (source - 8#64).toNat 8

/-- A fresh multi-field child exits with two actual publications, a complete
partial table, the original native bank, and strict copying progress. Pending
payload/queue data remain available in the concrete QueuedChild result. -/
theorem Head.finish_queued {sp sources pl initial copies q root before after payload log qs}
    (head : Head sp sources pl initial copies q root before)
    (post : SingleField.QueuedChild q root sp payload log qs pl before after)
    (footprint : QueuedExitFootprint q root payload log qs copies sources before) :
    Finished sp sources pl initial (⟨SingleField.child q root before,payload⟩ :: q :: copies) after ∧
      tailRemaining sources after < tailRemaining sources before := by
  have table := post.table head.table head.input.windows.source footprint.parentOutside footprint.suffixOutside
  refine ⟨⟨post.good,post.minstret,post.tick,post.code,?_,?_,table,
    post.complete head.complete footprint.otherHeaders,post.output.trans head.output,?_⟩,?_⟩
  · simpa only [head.saved.returnWord] using post.pc
  · simpa only [head.saved.restored] using post.registers
  · intro r noise outside
    have cover : ∀ n ∈ ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15])) ++
        (wrChain Enqueue.blocks ++ wrChain OldifyReturn.blocks), n ∈ exitWrites := by decide
    have prior : ∀ n ∈ tailWrites, n ∈ exitWrites := by decide
    exact (post.native r noise (fun n hn => outside n (cover n hn))).trans
      (head.native r noise (fun n hn => outside n (prior n hn)))
  · apply head.complete.progress table (fun p member => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) head.member head.fresh
    exact (table q (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1

end OCaml.Vm.Gc.SingleTail
