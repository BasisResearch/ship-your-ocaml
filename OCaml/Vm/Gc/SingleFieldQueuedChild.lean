import OCaml.Vm.Gc.ContextQueue
import OCaml.Vm.Gc.SingleFieldFreshLarge

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives

/-- Queue continuation ownership after the parent's prefix and child's
allocation; the collector heap invariant must supply these finite facts. -/
abbrev QueuedChildConditions (q : PendingCopy) (root sp payload : BitVec 64)
    (log : List WEntry) (qs : List PendingCopy) (pl : Place) (c : Config) :=
  Fresh.ContextQueueConditions (child q root c) q.target sp (childHeader q root c) payload
    (Enqueue.prefixLog q.source q.target root ++ log) qs pl c

/-- A queued fresh child has returned through the parent's current native
frame. The complete log includes parent forwarding, allocation, and insertion. -/
abbrev QueuedChild (q : PendingCopy) (root sp payload : BitVec 64)
    (log : List WEntry) (qs : List PendingCopy) (pl : Place) (before after : Config) :=
  Fresh.ContextQueued (child q root before) q.target sp payload
    (Enqueue.prefixLog q.source q.target root ++ log) qs pl
    ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15])) before after

/-- Actual ordinary parent prefix, fresh multi-field child allocation through
the exact-size route, queue insertion, and native return on the same frame. -/
theorem prepare_enqueue_child {q root sp domain size tag qs pl c}
    (input : Input q root c) (stack : gprGet c.σ 2 = some sp)
    (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c)
    (fresh : FreshChildConditions q root sp size tag c)
    (queue : QueuedChildConditions q root sp
      (Fresh.contextPayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
      (AllocWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) qs pl c) :
    FnSummary pc (fun d => d = c)
      (QueuedChild q root sp
        (Fresh.contextPayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        (AllocWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) qs pl c) :=
  Fresh.enqueue_after (prepare_allocate_child input stack constants even range fresh) queue

/-- The same complete queued-child route through the proved least-large-block
allocator alternative; all queue/native-frame composition is shared. -/
theorem prepare_enqueue_child_large {q root sp domain size tag qs pl c}
    (input : Input q root c) (stack : gprGet c.σ 2 = some sp)
    (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true)
    (range : YoungConditions q root domain c)
    (fresh : LargeFreshChildConditions q root sp size tag c)
    (queue : QueuedChildConditions q root sp
      (Fresh.contextLargePayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
      (AllocLargeWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) qs pl c) :
    FnSummary pc (fun d => d = c)
      (QueuedChild q root sp
        (Fresh.contextLargePayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        (AllocLargeWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) qs pl c) :=
  Fresh.enqueue_after (prepare_allocate_child_large input stack constants even range fresh) queue

end OCaml.Vm.Gc.SingleField
