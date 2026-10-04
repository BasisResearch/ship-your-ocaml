import OCaml.Vm.Gc.SingleFieldYoung
import OCaml.Vm.Gc.ForwardedReturn

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Observations and native-bank geometry for a captured child that already
has a forwarding header. These are data premises, not a child execution. -/
structure ForwardedConditions (q : PendingCopy) (root sp : BitVec 64) (c : Config) : Prop where
  header : word (forwardedSnapshot q root c) (child q root c - 8#64).toNat = 0
  headerRead : ReadWindow (child q root c - 8#64) 8
  pointerRead : ReadWindow (child q root c) 8
  rootWrite : WriteWindow q.target 8
  windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8
  outside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange [(q.target.toNat,8,word (forwardedSnapshot q root c) (child q root c).toNat)]
      (sp + BitVec.ofNat 64 off).toNat 8
  aligned : (OldifyReturn.returnWord sp (forwardedSnapshot q root c)).toNat % 4 = 0

/-- Reuse the proved zero-header route from the actual tail-loop boundary.
The epilogue restores the first invocation's bank; no prologue is replayed. -/
theorem YoungHead.forwarded_return {q root sp before middle}
    (head : YoungHead q root sp before middle)
    (conditions : ForwardedConditions q root sp before) :
    FnSummary Forwarded.pc (fun d => d = middle)
      (Forwarded.Returned (child q root before) q.target sp middle) := by
  have memory : middle.σ.mem = (forwardedSnapshot q root before).σ.mem := head.memory
  have input : Forwarded.Input (child q root before) q.target middle :=
    { good := head.good
      minstret := head.minstret
      tick := head.tick
      code := head.code
      registers := ⟨head.value,head.target,True.intro⟩
      header := by simpa only [word,memory] using conditions.header
      headerRead := conditions.headerRead
      pointerRead := conditions.pointerRead
      rootWrite := conditions.rootWrite }
  exact Forwarded.forwarded_return input head.stack conditions.windows
    (by simpa only [word,memory] using conditions.outside)
    (by simpa only [OldifyReturn.returnWord,word,memory] using conditions.aligned)

end OCaml.Vm.Gc.SingleField
