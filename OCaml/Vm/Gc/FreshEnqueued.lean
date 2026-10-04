import OCaml.Vm.Gc.FreshAllocated
import OCaml.Vm.Gc.FreshQueueCore
import OCaml.Vm.Gc.PendingPayload

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Memory at queue entry, computed from the initial memory and proved log. -/
def allocatedSnapshot (R : Nat → BitVec 64) (c : Config) : Config :=
  {c with σ := {c.σ with mem := writeLog c.σ.mem (allocationEffect R c)}}

def pending (R : Nat → BitVec 64) (c : Config) : PendingCopy :=
  ⟨R 10,allocatedPayload R c⟩

def enqueueEffect (R : Nat → BitVec 64) (qs : List PendingCopy) (c : Config) :=
  Enqueue.effect (R 10) (allocatedPayload R c) (R 11)
    (word (allocatedSnapshot R c) (R 10).toNat) (WorkQueue.head qs)

/-- Heap/stack separation for the large scanned-object queue route.
These finite initial-memory obligations are to be supplied by collector
ownership, including allocator freshness and the disjoint native stack. -/
structure EnqueueConditions (R : Nat → BitVec 64) (qs : List PendingCopy) (pl : Place)
    (c : Config) : Prop where
  queue : WorkQueue.EnqueueConditions (pending R c) qs pl (R 11)
    (sizeWord (word c (R 10 - 8#64).toNat)) (allocatedSnapshot R c)
  allocationOutside : ∀ cell ∈ OldifyEntry.saves,
    OutLRange (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c))
      (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8
  enqueueOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (enqueueEffect R qs c) (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8
  sourceOutside : OutLRange (allocationEffect R c) (R 10).toNat 8
  aligned : (R 1).toNat % 4 = 0

theorem Allocated.toResult {R before after} (post : Allocated R before after) :
    AllocationResult R (allocatedPayload R before)
      (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before after :=
  ⟨post.good,post.minstret,post.tick,post.code,post.pc,post.registers,post.stack,post.constants,
    post.memory,post.output,post.native⟩

theorem EnqueueConditions.toQueue {R qs pl c} (conditions : EnqueueConditions R qs pl c) :
    QueueConditions R (allocatedPayload R c)
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) qs pl c :=
  ⟨conditions.queue,conditions.allocationOutside,conditions.enqueueOutside,conditions.sourceOutside,conditions.aligned⟩

/-- The allocator preserves each original oldify save slot under the named
stack footprint obligation. Readback uses the same shared bank lemma. -/
theorem Allocated.saved {R before after} (post : Allocated R before after)
    (input : OldifyEntry.Input R before)
    (outside : ∀ cell ∈ OldifyEntry.saves,
      OutLRange (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before))
        (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8)
    (cell : Nat × Nat) (member : cell ∈ OldifyEntry.saves) :
    word after (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat = R cell.1 :=
  post.toResult.saved input outside cell member

structure Enqueued (R : Nat → BitVec 64) (qs : List PendingCopy) (pl : Place)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  memory : after.σ.mem = writeLog before.σ.mem
    (allocationEffect R before ++ enqueueEffect R qs before)
  data : WorkQueue.EnqueuePost (pending R before) qs pl (R 11) (word before (R 10).toNat) after
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ ((1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15]) ++
      (wrChain Enqueue.blocks ++ wrChain OldifyReturn.blocks), (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete actual oldify entry, allocation, forwarding, queue insertion
and native return for a fresh scanned block with more than one field. -/
theorem enqueue_fresh {R domain size tag c qs pl} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c) (conditions : EnqueueConditions R qs pl c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (Enqueued R qs pl c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh input allocation).run
  intro middle allocated
  obtain ⟨after,run,post⟩ := (allocated.toResult.enqueue input.entry conditions.toQueue).run middle ⟨allocated.pc,rfl⟩
  exact ⟨after,run,⟨post.good,post.minstret,post.tick,post.code,post.pc,post.registers,
    post.memory,post.data,post.output,post.native⟩⟩

theorem Enqueued.toQueue {R qs pl before after} (post : Enqueued R qs pl before after) :
    QueueResult R (allocatedPayload R before)
      (AllocWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) qs pl before after :=
  ⟨post.good,post.minstret,post.tick,post.code,post.pc,post.registers,
    post.memory,post.data,post.output,post.native⟩

/-- The complete fresh-object route establishes the represented grey payload,
using the relocation Eqv interface and original source field observations. -/
theorem Enqueued.payload {R qs pl before after cp tag fields}
    (post : Enqueued R qs pl before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag fields))
    (outside : ∀ i v, fields[i]? = some v → i ≠ 0 →
      OutLRange (allocationEffect R before ++ enqueueEffect R qs before)
        ((R 10).toNat + 8 * i) 8) :
    (pendingPayload (pending R before) fields).P pl (allocatedPayload R before).toNat after :=
  post.toQueue.payload object outside

end OCaml.Vm.Gc.Fresh
