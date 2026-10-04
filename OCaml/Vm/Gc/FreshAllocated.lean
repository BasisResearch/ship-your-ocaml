import OCaml.Vm.Gc.FreshAllocator
import OCaml.Vm.Gc.AllocationFootprint
import OCaml.Vm.Gc.Generated.Enqueue

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initial memory after the decoded oldify native-save stores. -/
def oldifySnapshot (R : Nat → BitVec 64) (c : Config) : Config :=
  { c with σ := { c.σ with mem := writeLog c.σ.mem (OldifyEntry.saveLog OldifyEntry.saves R) } }

def allocatedPayload (R : Nat → BitVec 64) (c : Config) : BitVec 64 :=
  BestFitSmall.first (allocatorRegs R c 10)
    (AllocWrapper.prepared (allocatorRegs R c) (oldifySnapshot R c))

def allocationEffect (R : Nat → BitVec 64) (c : Config) : List WEntry :=
  OldifyEntry.saveLog OldifyEntry.saves R ++
    AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)

/-- Exact-size allocation geometry on explicit initial-memory snapshots.
The general heap/free-list invariant must supply these conditions; none
assumes an execution of the allocator. -/
structure AllocationConditions (R : Nat → BitVec 64) (c : Config) : Prop where
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  windows : AllocEntry.Windows (allocatorRegs R c)
  pointer : word c Layout.sym_caml_fl_p_allocate = BestFitSmall.pc
  outer : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) Layout.sym_caml_fl_p_allocate 8
  inner : OutLRange (AllocEntry.prefixLog (allocatorRegs R c)) Layout.sym_caml_fl_p_allocate 8
  wrapper : AllocWrapper.Conditions (allocatorRegs R c) (oldifySnapshot R c)

structure Allocated (R : Nat → BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt Enqueue.pc after
  registers : GHolds after.σ (Enqueue.regs (R 10) (allocatedPayload R before) (R 11)
    (sizeWord (word before (R 10 - 8#64).toNat)))
  stack : gprGet after.σ 2 = some (OldifyEntry.frameSp R)
  memory : after.σ.mem = writeLog before.σ.mem (allocationEffect R before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ (1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Execute fresh scanned-object oldify, including its actual allocating
call and complete exact-size allocation, to the forwarding/copy queue code. -/
theorem allocate_fresh {R domain size tag c} (input : EntryInput R domain size tag c)
    (conditions : AllocationConditions R c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (Allocated R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_allocation input).run
  intro middle entered
  have memory : middle.σ.mem = (oldifySnapshot R c).σ.mem := entered.memory
  have freeCode : Code.Bf_allocateLoaded middle.σ.mem := by
    rw [entered.memory]
    apply image_writeLog Code.bf_allocate_transport conditions.freeCode
    intro e member
    exact Nat.le_trans (by decide) (OldifyEntry.saveLog_high input.entry.windows e member)
  have allocInput : AllocWrapper.Input (allocatorRegs R c) middle :=
    { toInput := entered.allocator_input input.entry.windows conditions.code conditions.windows
        conditions.pointer conditions.outer conditions.inner
      toConditions := conditions.wrapper.of_memory memory
      freeListCode := freeCode }
  obtain ⟨after,run,allocated⟩ := (AllocWrapper.allocate allocInput).run middle ⟨entered.pc,rfl⟩
  have effect := AllocWrapper.effect_of_memory (R := allocatorRegs R c) memory
  have preparedMemory := AllocWrapper.prepared_memory (R := allocatorRegs R c) memory
  have payload : BestFitSmall.first (allocatorRegs R c 10)
      (AllocWrapper.prepared (allocatorRegs R c) middle) = allocatedPayload R c := by
    simp only [BestFitSmall.first,word,preparedMemory,allocatedPayload]
  have kept : GHolds after.σ [(24,R 10 - 8#64),(22,1),
      (25,sizeWord (word c (R 10 - 8#64).toNat))] := by
    apply gholds_of_frame allocated.native _ (by change KeysOK [24,22,25]; decide)
      (by change ∀ n ∈ [24,22,25], ∀ q ∈ noiseRegs, (q == gprReg n) = false; decide)
      (by change ∀ n ∈ [24,22,25], ∀ m ∈ [1,2,8,9,10,11,12,13,14,15],
          (gprReg m == gprReg n) = false; decide)
    exact ⟨gholds_lookup _ entered.arguments rfl,gholds_lookup _ entered.carried rfl,
      gholds_lookup _ entered.arguments rfl,True.intro⟩
  refine ⟨after,run,⟨allocated.good,allocated.minstret,allocated.tick,?_,?_,?_,
    gholds_lookup _ allocated.registers rfl,?_,allocated.output.trans entered.output,?_⟩⟩
  · rw [allocated.memory]
    apply image_writeLog Code.caml_oldify_one_transport entered.code
    intro e member
    exact Nat.le_trans (by decide) (AllocWrapper.effect_high conditions.windows allocInput.toConditions e member)
  · exact allocated.pc
  · exact ⟨payload ▸ allocated.result,gholds_lookup _ allocated.registers rfl,
      gholds_lookup _ allocated.registers rfl,gholds_lookup _ kept rfl,
      gholds_lookup _ kept rfl,gholds_lookup _ kept rfl,True.intro⟩
  · rw [allocated.memory,effect,entered.memory,allocationEffect,writeLog_append]
  · intro r noise outside
    exact (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (entered.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.Fresh
