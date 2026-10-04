import OCaml.Vm.Gc.FreshAllocated
import OCaml.Vm.Gc.AllocLargeWrapper

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Initial-memory conditions for fresh oldify's least-large-block allocation.
The general ownership invariant supplies the memory geometry and separation. -/
structure LargeAllocationConditions (R : Nat → BitVec 64) (c : Config) : Prop where
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  ffsCode : Code.FfsLoaded c.σ.mem
  splitCode : Code.Bf_splitLoaded c.σ.mem
  windows : AllocEntry.Windows (allocatorRegs R c)
  pointer : word c Layout.sym_caml_fl_p_allocate = BestFitSmall.pc
  outer : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R) Layout.sym_caml_fl_p_allocate 8
  inner : OutLRange (AllocEntry.prefixLog (allocatorRegs R c)) Layout.sym_caml_fl_p_allocate 8
  wrapper : AllocLargeWrapper.Conditions (allocatorRegs R c) (oldifySnapshot R c)

def largePayload (R : Nat → BitVec 64) (c : Config) :=
  AllocLargeWrapper.resultHeader (allocatorRegs R c) (oldifySnapshot R c) + BitVec.ofNat 64 Layout.header_bytes

def largeAllocationEffect (R : Nat → BitVec 64) (c : Config) :=
  OldifyEntry.saveLog OldifyEntry.saves R ++
    AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)

abbrev LargeAllocated (R : Nat → BitVec 64) (before after : Config) :=
  AllocationResult R (largePayload R before)
    (AllocLargeWrapper.effect (allocatorRegs R before) (oldifySnapshot R before)) before after

/-- Actual fresh-oldify entry through the allocating wrapper, least-large-block
split and wrapper return, reaching the same queue entry as exact-size allocation. -/
theorem allocate_fresh_large {R domain size tag c} (input : EntryInput R domain size tag c)
    (conditions : LargeAllocationConditions R c) :
    FnSummary OldifyEntry.pc (fun d => d = c) (LargeAllocated R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_allocation input).run
  intro middle entered
  have memory : middle.σ.mem = (oldifySnapshot R c).σ.mem := entered.memory
  have allocInput : AllocLargeWrapper.Input (allocatorRegs R c) middle :=
    { toInput := entered.allocator_input input.entry.windows conditions.code conditions.windows
        conditions.pointer conditions.outer conditions.inner
      toConditions := conditions.wrapper.of_memory memory
      freeCode := entered.toPrepared.image input.entry.windows Code.bf_allocate_transport (by decide) conditions.freeCode
      ffsCode := entered.toPrepared.image input.entry.windows Code.ffs_transport (by decide) conditions.ffsCode
      splitCode := entered.toPrepared.image input.entry.windows Code.bf_split_transport (by decide) conditions.splitCode }
  obtain ⟨after,run,allocated⟩ := (AllocLargeWrapper.allocate allocInput).run middle ⟨entered.pc,rfl⟩
  have done := entered.finish allocated (AllocLargeWrapper.effect_high conditions.windows allocInput.toConditions)
  change AllocationResult R (_ + _) (AllocLargeWrapper.effect (allocatorRegs R c) middle) c after at done
  rw [AllocLargeWrapper.effect_of_memory memory,AllocLargeWrapper.resultHeader_of_memory memory] at done
  exact ⟨after,run,done⟩

end OCaml.Vm.Gc.Fresh
