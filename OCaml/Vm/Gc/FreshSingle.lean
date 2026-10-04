import OCaml.Vm.Gc.FreshEnqueued
import OCaml.Vm.Gc.FreshLargeAllocated
import OCaml.Vm.Gc.SingleFieldReturn
import OCaml.Vm.Gc.NativeRestore

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

def singleEffect (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry) (c : Config) :=
  SingleField.effect (queuePending R target) (R 11) (queueSnapshot R log c)

/-- Initial-memory geometry for a single-field object whose child is
immediate. The collector ownership invariant supplies the separation. -/
structure SingleConditions (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (c : Config) : Prop where
  single : sizeWord (word c (R 10 - 8#64).toNat) = 1
  prefixWindows : WorkQueue.PrefixWindows (queuePending R target) (R 11)
  windows : StoreReturn.Windows (OldifyEntry.frameSp R)
    (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) target
  allocationOutside : ∀ cell ∈ OldifyEntry.saves,
    OutLRange log (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8
  prefixOutside : ∀ off ∈ OldifyReturn.offsets,
    OutLRange (Enqueue.prefixLog (R 10) target (R 11))
      (OldifyEntry.frameSp R + BitVec.ofNat 64 off).toNat 8
  immediate : ChildClassify.even
    (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) = false
  aligned : (R 1).toNat % 4 = 0

structure SingleResult (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  memory : after.σ.mem = writeLog before.σ.mem
    ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ singleEffect R target log before)
  value : word after target.toNat =
    SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ (wrChain StoreReturn.blocks ++ [8,9,14,15]) ++
      ((1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15]), (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared complete single-field continuation from either actual allocator
result, identifying original caller registers through the decoded save bank. -/
theorem AllocationResult.single_immediate {R target log c middle}
    (allocated : AllocationResult R target log c middle) (input : OldifyEntry.Input R c)
    (conditions : SingleConditions R target log c) :
    FnSummary Enqueue.pc (fun d => d = middle) (SingleResult R target log c) := by
  constructor
  intro start pre
  rcases pre with ⟨_,equal⟩
  subst start
  have memory : middle.σ.mem = (queueSnapshot R log c).σ.mem := by
    simpa only [queueSnapshot] using allocated.memory
  have saved := allocated.saved input conditions.allocationOutside
  have returnWord : StoreReturn.returnWord (OldifyEntry.frameSp R) middle = R 1 :=
    saved StoreReturn.returnSlots.head! (by decide)
  have singleInput : SingleField.Input (queuePending R target) (R 11) middle :=
    ⟨allocated.good,allocated.tick,allocated.minstret,allocated.code,
      by simpa only [conditions.single,queuePending] using allocated.registers,conditions.prefixWindows⟩
  have returns : SingleField.ReturnConditions (queuePending R target) (R 11) (OldifyEntry.frameSp R) middle :=
    { windows := by simpa only [SingleField.child_of_memory memory,queuePending] using conditions.windows
      prefixOutside := conditions.prefixOutside
      aligned := returnWord ▸ conditions.aligned
      immediate := by simpa only [SingleField.child_of_memory memory,queuePending] using conditions.immediate }
  obtain ⟨after,run,returned⟩ := (SingleField.return_immediate singleInput allocated.stack returns).run middle ⟨allocated.pc,rfl⟩
  refine ⟨after,run,⟨returned.good,returned.tick,returned.minstret,returned.code,?_,
    StoreReturn.original_caller saved returned.registers,?_,?_,returned.output.trans allocated.output,?_⟩⟩
  · simpa only [returnWord] using returned.pc
  · rw [returned.memory,SingleField.effect_of_memory memory,allocated.memory,singleEffect,writeLog_append]
    simp only [writeLog_append]
  · simpa only [SingleField.child_of_memory memory,queuePending] using returned.value
  · intro r noise outside
    exact (returned.native r noise (fun n hn => outside n (List.mem_append_left _ hn))).trans
      (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn)))

/-- Whole fresh oldify through exact-size allocation and immediate single-field
continuation, returning to the original native caller. -/
theorem single_fresh {R domain size tag c} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : SingleConditions R (allocatedPayload R c)
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (SingleResult R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh input allocation).run
  intro middle allocated
  exact (allocated.toResult.single_immediate input.entry conditions).run middle ⟨allocated.pc,rfl⟩

/-- The same complete single-field continuation after least-large-block allocation. -/
theorem single_fresh_large {R domain size tag c} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : SingleConditions R (largePayload R c)
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (SingleResult R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh_large input allocation).run
  intro middle allocated
  exact (allocated.single_immediate input.entry conditions).run middle ⟨allocated.pc,rfl⟩

end OCaml.Vm.Gc.Fresh
