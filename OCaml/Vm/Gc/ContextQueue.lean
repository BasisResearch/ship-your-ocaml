import OCaml.Vm.Gc.AllocationContext
import OCaml.Vm.Gc.EnqueueReturn
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def contextSnapshot (log : List WEntry) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem log}}

def contextQueueEffect (source target root : BitVec 64) (log : List WEntry)
    (qs : List PendingCopy) (c : Config) :=
  Enqueue.effect source target root (word (contextSnapshot log c) source.toNat) (WorkQueue.head qs)

/-- Queue ownership and native-frame footprints for allocation on an already
established oldify frame. The snapshot includes the allocation stores, while
the saved bank and original source observations refer to the tail entry. -/
structure ContextQueueConditions (source root sp hd target : BitVec 64) (log : List WEntry)
    (qs : List PendingCopy) (pl : Place) (c : Config) : Prop where
  queue : WorkQueue.EnqueueConditions ⟨source,target⟩ qs pl root (sizeWord hd) (contextSnapshot log c)
  allocationBank : ∀ off ∈ OldifyReturn.offsets, OutLRange log (sp + BitVec.ofNat 64 off).toNat 8
  returnRead : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8
  enqueueBank : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (contextQueueEffect source target root log qs c) (sp + BitVec.ofNat 64 off).toNat 8
  sourceOutside : OutLRange log source.toNat 8
  aligned : (OldifyReturn.returnWord sp c).toNat % 4 = 0

/-- A fresh multi-field child is now pending in the intrusive queue and has
returned through the tail entry's original saved bank. Its suffix remains
for mopup; allocation and queue insertion are both actual machine effects. -/
structure ContextQueued (source root sp target : BitVec 64) (log : List WEntry)
    (qs : List PendingCopy) (pl : Place) (writes : List Nat) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (OldifyReturn.returnWord sp before) after
  registers : GHolds after.σ (OldifyReturn.restored sp before)
  memory : after.σ.mem = writeLog before.σ.mem (log ++ contextQueueEffect source target root log qs before)
  data : WorkQueue.EnqueuePost ⟨source,target⟩ qs pl root (word before source.toNat) after
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes ++ (wrChain Enqueue.blocks ++ wrChain OldifyReturn.blocks), (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared continuation for a multi-field allocation on the existing native
frame. The concrete queue machine summary supplies all forwarding/link stores
and the epilogue; finite footprints identify the earlier bank and payload. -/
theorem ContextAllocated.enqueue {source root sp hd target log qs pl writes before middle}
    (allocated : ContextAllocated source root sp hd target log before middle writes)
    (conditions : ContextQueueConditions source root sp hd target log qs pl before) :
    FnSummary Enqueue.pc (fun c => c = middle)
      (ContextQueued source root sp target log qs pl writes before) := by
  constructor
  intro c pre
  rcases pre with ⟨_,equal⟩
  subst c
  have memory : middle.σ.mem = (contextSnapshot log before).σ.mem := allocated.memory
  have input : WorkQueue.EnqueueInput ⟨source,target⟩ qs pl root (sizeWord hd) middle :=
    { toEnqueueConditions := conditions.queue.of_memory memory
      good := allocated.good
      minstret := allocated.minstret
      tick := allocated.tick
      code := allocated.code
      registers := allocated.registers }
  have bank := OldifyReturn.SavedSame.of_writeLog allocated.memory conditions.allocationBank
  have outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange (Enqueue.effect source target root (word middle source.toNat) (WorkQueue.head qs))
        (sp + BitVec.ofNat 64 off).toNat 8 := by
    simpa only [contextQueueEffect,word,memory] using conditions.enqueueBank
  have aligned : (OldifyReturn.returnWord sp middle).toNat % 4 = 0 := by
    rw [bank.returnWord]; exact conditions.aligned
  obtain ⟨after,run,returned⟩ := (WorkQueue.enqueue_return input allocated.stack conditions.returnRead outside aligned).run
    middle ⟨allocated.pc,rfl⟩
  have sourceSame : word middle source.toNat = word before source.toNat := by
    simp only [word,allocated.memory,bytesT_writeLog_out _ conditions.sourceOutside]
  refine ⟨after,run,⟨returned.good,returned.minstret,returned.tick,returned.code,?_,?_,?_,?_,
    returned.output.trans allocated.output,?_⟩⟩
  · simpa only [bank.returnWord] using returned.pc
  · simpa only [bank.restored] using returned.registers
  · rw [returned.memory,allocated.memory,writeLog_append]
    simp only [contextQueueEffect,word,memory]
  · simpa only [sourceSame] using returned.data
  · intro r noise outside
    exact (returned.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (allocated.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

/-- Splice any actual allocation summary into the shared queue continuation. -/
theorem enqueue_after {entry source root sp hd target log qs pl writes before}
    (allocation : FnSummary entry (fun c => c = before)
      (fun after => ContextAllocated source root sp hd target log before after writes))
    (conditions : ContextQueueConditions source root sp hd target log qs pl before) :
    FnSummary entry (fun c => c = before) (ContextQueued source root sp target log qs pl writes before) := by
  constructor
  apply Vsa.Logic.Triple.seq allocation.run
  intro middle allocated
  exact (allocated.enqueue conditions).run middle ⟨allocated.pc,rfl⟩

/-- The queued child retains every original pending field: the first is in
the copy and the deferred suffix remains in the source for mopup. -/
theorem ContextQueued.payload {source root sp target log qs pl writes before after cp tag fields}
    (post : ContextQueued source root sp target log qs pl writes before after)
    (object : ObjAt before pl cp source.toNat (.block tag fields))
    (outside : ∀ i v, fields[i]? = some v → i ≠ 0 →
      OutLRange (log ++ contextQueueEffect source target root log qs before) (source.toNat + 8 * i) 8) :
    (pendingPayload ⟨source,target⟩ fields).P pl target.toNat after :=
  pendingPayload_of_writeLog object post.data.first post.memory outside

end OCaml.Vm.Gc.Fresh
