import OCaml.Vm.Gc.SingleFieldTable
import OCaml.Vm.Gc.TailProgress

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Heap/native ownership facts for a fresh-child back edge. These describe
finite memory footprints and next write windows, not execution or an invariant
post-state. The enclosing heap invariant must supply them. -/
structure BackEdgeConditions (q : PendingCopy) (root sp payload : BitVec 64)
    (copies : List PendingCopy) (sources : List (BitVec 64)) (log : List WEntry) (c : Config) : Prop where
  nextWindows : WorkQueue.PrefixWindows ⟨child q root c,payload⟩ q.target
  member : q.source ∈ sources
  fresh : word c (q.source - 8#64).toNat ≠ 0
  nextMember : child q root c ∈ sources
  headerOutside : ∀ source ∈ sources, source ≠ q.source →
    OutLRange (Enqueue.prefixLog q.source q.target root) (source - 8#64).toNat 8
  allocationHeaders : ∀ source ∈ sources, OutLRange log (source - 8#64).toNat 8
  tableOutside : ForwardingTable.Outside copies (Enqueue.prefixLog q.source q.target root)
  allocationTable : ForwardingTable.Outside (q :: copies) log
  bankOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (Enqueue.prefixLog q.source q.target root ++ log) (sp + BitVec.ofNat 64 off).toNat 8

/-- Actual next forwarding entry, a larger published table, the same native
bank and a strictly smaller copying rank. Pending typed payloads remain a
separate component of the full collector invariant. -/
structure BackEdgeResult (q : PendingCopy) (root sp payload : BitVec 64)
    (copies : List PendingCopy) (sources : List (BitVec 64)) (log : List WEntry) (pl : Place)
    (before after : Config) : Prop where
  allocated : Fresh.ContextAllocated (child q root before) q.target sp (childHeader q root before)
    payload (Enqueue.prefixLog q.source q.target root ++ log) before after
    ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15]))
  size : Fresh.sizeWord (childHeader q root before) = 1
  nextWindows : WorkQueue.PrefixWindows ⟨child q root before,payload⟩ q.target
  member : child q root before ∈ sources
  fresh : word after (child q root before - 8#64).toNat ≠ 0
  table : (ForwardingTable.eqv (q :: copies)).P pl 0 after
  saved : OldifyReturn.SavedSame sp before after
  decrease : tailRemaining sources after < tailRemaining sources before

/-- The next iteration's full register and RAM interface comes from the
real allocation result, not an assumed recursive call. -/
theorem BackEdgeResult.next_input {q root sp payload copies sources log pl before after}
    (post : BackEdgeResult q root sp payload copies sources log pl before after) :
    Input ⟨child q root before,payload⟩ q.target after :=
  ⟨post.allocated.good,post.allocated.tick,post.allocated.minstret,post.allocated.code,
    by simpa only [post.size] using post.allocated.registers,post.nextWindows⟩

/-- Shared back-edge invariant step for either actual allocator. -/
theorem complete_backedge {q root sp payload copies sources log pl tag before after}
    (post : Fresh.ContextAllocated (child q root before) q.target sp (childHeader q root before)
      payload (Enqueue.prefixLog q.source q.target root ++ log) before after
      ([8,9,14,15,25] ++ ((1 :: wrChain Fresh.blocks) ++ [1,2,8,9,10,11,12,13,14,15])))
    (header : FreshChildHeader q root sp 1 tag before)
    (window : WriteWindow q.source 8) (table : (ForwardingTable.eqv copies).P pl 0 before)
    (conditions : BackEdgeConditions q root sp payload copies sources log before) :
    BackEdgeResult q root sp payload copies sources log pl before after := by
  have headerSame : word after (child q root before - 8#64).toNat = childHeader q root before := by
    rw [word,post.memory,writeLog_append,
      bytesT_writeLog_out _ (conditions.allocationHeaders _ conditions.nextMember)]
    rfl
  have nonzero := (Fresh.header_conditions header.header header.positive header.scanned).1
  refine ⟨post,?_,conditions.nextWindows,conditions.nextMember,?_,
    ForwardingTable.publish_then table post.memory window conditions.tableOutside conditions.allocationTable,
    OldifyReturn.SavedSame.of_writeLog post.memory conditions.bankOutside,
    forwarding_then_decreases post.memory window conditions.member conditions.fresh
      conditions.headerOutside conditions.allocationHeaders⟩
  · exact (Fresh.arguments_of_header header.header).1
  · rwa [headerSame]

/-- Parent forwarding and exact-size child allocation establish a concrete
back edge with strict progress and the extended partial forwarding table. -/
theorem backedge_exact {q root sp domain tag copies sources pl c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true) (range : YoungConditions q root domain c)
    (fresh : FreshChildConditions q root sp 1 tag c) (table : (ForwardingTable.eqv copies).P pl 0 c)
    (conditions : BackEdgeConditions q root sp
      (Fresh.contextPayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
      copies sources (AllocWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) c) :
    FnSummary pc (fun d => d = c)
      (BackEdgeResult q root sp
        (Fresh.contextPayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        copies sources (AllocWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) pl c) := by
  apply (prepare_allocate_child input stack constants even range fresh).weaken (fun _ h => h)
  intro after allocated
  exact complete_backedge allocated fresh.toFreshChildHeader input.windows.source table conditions

/-- The least-large-block alternative establishes the same back-edge invariant. -/
theorem backedge_large {q root sp domain tag copies sources pl c} (input : Input q root c)
    (stack : gprGet c.σ 2 = some sp) (constants : GHolds c.σ Fresh.loopConstants)
    (even : ChildClassify.even (child q root c) = true) (range : YoungConditions q root domain c)
    (fresh : LargeFreshChildConditions q root sp 1 tag c) (table : (ForwardingTable.eqv copies).P pl 0 c)
    (conditions : BackEdgeConditions q root sp
      (Fresh.contextLargePayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
      copies sources (AllocLargeWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) c) :
    FnSummary pc (fun d => d = c)
      (BackEdgeResult q root sp
        (Fresh.contextLargePayload (child q root c) q.target sp (childHeader q root c) (forwardedSnapshot q root c))
        copies sources (AllocLargeWrapper.effect (childAllocatorRegs q root sp c) (forwardedSnapshot q root c)) pl c) := by
  apply (prepare_allocate_child_large input stack constants even range fresh).weaken (fun _ h => h)
  intro after allocated
  exact complete_backedge allocated fresh.toFreshChildHeader input.windows.source table conditions

end OCaml.Vm.Gc.SingleField
