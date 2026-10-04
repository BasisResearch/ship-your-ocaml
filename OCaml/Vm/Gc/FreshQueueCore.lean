import OCaml.Vm.Gc.FreshAllocationCore
import OCaml.Vm.Gc.EnqueueReturn
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def queueSnapshot (R : Nat → BitVec 64) (log : List WEntry) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (OldifyEntry.saveLog OldifyEntry.saves R ++ log)}}

def queuePending (R : Nat → BitVec 64) (target : BitVec 64) : PendingCopy := ⟨R 10,target⟩

def queueEffect (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (qs : List PendingCopy) (c : Config) :=
  Enqueue.effect (R 10) target (R 11) (word (queueSnapshot R log c) (R 10).toNat) (WorkQueue.head qs)

/-- Heap/stack separation for the large scanned-object queue route.
These finite initial-memory obligations are to be supplied by collector
ownership, including allocator freshness and the disjoint native stack. -/
structure QueueConditions (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (qs : List PendingCopy) (pl : Place)
    (c : Config) : Prop where
  queue : WorkQueue.EnqueueConditions (queuePending R target) qs pl (R 11)
    (sizeWord (word c (R 10 - 8#64).toNat)) (queueSnapshot R log c)
  allocationOutside : ∀ cell ∈ OldifyEntry.saves,
    OutLRange log
      (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8
  enqueueOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (queueEffect R target log qs c) (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8
  sourceOutside : OutLRange ((OldifyEntry.saveLog OldifyEntry.saves R ++ log)) (R 10).toNat 8
  aligned : (R 1).toNat % 4 = 0

/-- The allocator preserves each original oldify save slot under the named
stack footprint obligation. Readback uses the same shared bank lemma. -/
theorem AllocationResult.saved {R target log before after} (post : AllocationResult R target log before after)
    (input : OldifyEntry.Input R before)
    (outside : ∀ cell ∈ OldifyEntry.saves,
      OutLRange log
        (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8)
    (cell : Nat × Nat) (member : cell ∈ OldifyEntry.saves) :
    word after (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 := by
  change bytesT after.σ.mem _ 8 = _
  rw [post.memory,writeLog_append,bytesT_writeLog_out _ (outside cell member)]
  exact OldifyEntry.saveShape.read before.σ.mem (OldifyEntry.frameSp R) R input.windows cell member

structure QueueResult (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (qs : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  memory : after.σ.mem = writeLog before.σ.mem
    ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ queueEffect R target log qs before)
  data : WorkQueue.EnqueuePost (queuePending R target) qs pl (R 11) (word before (R 10).toNat) after
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ ((1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15]) ++
      (wrChain Enqueue.blocks ++ wrChain OldifyReturn.blocks), (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared forwarding, queue insertion and original native return from
an actual fresh allocation result, for either proved allocator route. -/
theorem AllocationResult.enqueue {R target log c middle qs pl}
    (allocated : AllocationResult R target log c middle)
    (input : OldifyEntry.Input R c) (conditions : QueueConditions R target log qs pl c) :
    FnSummary Enqueue.pc (fun d => d = middle) (QueueResult R target log qs pl c) := by
  constructor
  intro start pre
  rcases pre with ⟨_,same⟩
  subst start
  have memory : middle.σ.mem = (queueSnapshot R log c).σ.mem := by
    simpa only [queueSnapshot] using allocated.memory
  have queueInput : WorkQueue.EnqueueInput (queuePending R target) qs pl (R 11)
      (sizeWord (word c (R 10 - 8#64).toNat)) middle :=
    { toEnqueueConditions := conditions.queue.of_memory memory
      good := allocated.good
      minstret := allocated.minstret
      registers := allocated.registers
      tick := allocated.tick
      code := allocated.code }
  have saved := allocated.saved input conditions.allocationOutside
  have returnedWord : OldifyReturn.returnWord (OldifyEntry.frameSp R) middle = R 1 :=
    saved OldifyReturn.slots.head! (by decide)
  have windows : ∀ off ∈ OldifyReturn.offsets,
      ReadWindow (OldifyEntry.frameSp R + BitVec.ofNat 64 off) 8 := by
    intro off member
    rw [OldifyReturn.offsets_eq] at member
    obtain ⟨cell,hc,rfl⟩ := List.mem_map.mp member
    exact (input.windows cell (OldifyEntry.restore_slots cell hc)).read
  have source : word middle (R 10).toNat = word c (R 10).toNat := by
    change bytesT middle.σ.mem _ 8 = _
    rw [allocated.memory,bytesT_writeLog_out _ conditions.sourceOutside]
    rfl
  have outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange (Enqueue.effect (queuePending R target).source (queuePending R target).target (R 11)
        (word middle (queuePending R target).source.toNat) (WorkQueue.head qs))
        (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8 := by
    simpa only [queueEffect,queuePending,word,memory] using conditions.enqueueOutside
  obtain ⟨after,run,returned⟩ := (WorkQueue.enqueue_return queueInput allocated.stack windows
    outside (returnedWord ▸ conditions.aligned)).run middle ⟨allocated.pc,rfl⟩
  refine ⟨after,run,⟨returned.good,returned.minstret,returned.tick,returned.code,?_,?_,?_,?_,
    returned.output.trans allocated.output,?_⟩⟩
  · simpa only [returnedWord] using returned.pc
  · simpa only [OldifyEntry.restored_of_saved saved] using returned.registers
  · rw [returned.memory,allocated.memory,writeLog_append]
    simp only [queueEffect,queuePending,word,memory,writeLog_append]
  · simpa only [queuePending,source] using returned.data
  · intro r noise outside
    exact (returned.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (allocated.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

/-- The complete fresh-object route establishes the represented grey payload,
using the relocation Eqv interface and original source field observations. -/
theorem QueueResult.payload {R target log qs pl before after cp tag fields}
    (post : QueueResult R target log qs pl before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag fields))
    (outside : ∀ i v, fields[i]? = some v → i ≠ 0 →
      OutLRange ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ queueEffect R target log qs before)
        ((R 10).toNat + 8 * i) 8) :
    (pendingPayload (queuePending R target) fields).P pl target.toNat after := by
  exact pendingPayload_of_writeLog (q := queuePending R target) object post.data.first post.memory outside

end OCaml.Vm.Gc.Fresh
