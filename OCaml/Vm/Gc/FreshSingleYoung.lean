import OCaml.Vm.Gc.FreshSingleData
import OCaml.Vm.Gc.SingleFieldYoung

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Prefix geometry and actual nursery observations for a young captured
child. No child return or destination payload is assumed. -/
structure YoungSingleConditions (R : Nat → BitVec 64) (target domain : BitVec 64)
    (log : List WEntry) (c : Config) : Prop where
  single : sizeWord (word c (R 10 - 8#64).toNat) = 1
  prefixWindows : WorkQueue.PrefixWindows (queuePending R target) (R 11)
  even : ChildClassify.even (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log c)) = true
  range : SingleField.YoungConditions (queuePending R target) (R 11) domain (queueSnapshot R log c)

/-- The first native invocation has allocated and forwarded its single-field
parent and now tail-processes the captured child using the same native frame. -/
structure YoungSingleResult (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt OldifyYoung.exitPc after
  value : gprGet after.σ 8 = some (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before))
  destination : gprGet after.σ 9 = some target
  stack : gprGet after.σ 2 = some (OldifyEntry.frameSp R)
  constants : GHolds after.σ loopConstants
  memory : after.σ.mem = writeLog before.σ.mem
    ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++ Enqueue.prefixLog (R 10) target (R 11))
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ [8,9,14,15,25] ++ ((1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15]),
      (gprReg n == r) = false) → after.σ.regs.get? r = before.σ.regs.get? r

theorem AllocationResult.single_young {R target domain log c middle}
    (allocated : AllocationResult R target log c middle)
    (conditions : YoungSingleConditions R target domain log c) :
    FnSummary Enqueue.pc (fun d => d = middle) (YoungSingleResult R target log c) := by
  constructor
  intro start pre
  rcases pre with ⟨_,equal⟩
  subst start
  have memory : middle.σ.mem = (queueSnapshot R log c).σ.mem := by
    simpa only [queueSnapshot] using allocated.memory
  have input : SingleField.Input (queuePending R target) (R 11) middle :=
    ⟨allocated.good,allocated.tick,allocated.minstret,allocated.code,
      by simpa only [conditions.single,queuePending] using allocated.registers,conditions.prefixWindows⟩
  have even : ChildClassify.even (SingleField.child (queuePending R target) (R 11) middle) = true := by
    simpa only [SingleField.child_of_memory memory] using conditions.even
  obtain ⟨after,run,head⟩ := (SingleField.prepare_young input allocated.stack allocated.constants even
    (conditions.range.of_memory memory)).run middle ⟨allocated.pc,rfl⟩
  refine ⟨after,run,⟨head.good,head.tick,head.minstret,head.code,head.pc,?_,head.target,head.stack,
    head.constants,?_,head.output.trans allocated.output,?_⟩⟩
  · simpa only [SingleField.child_of_memory memory] using head.value
  · rw [head.memory,allocated.memory]
    simp only [writeLog_append,queuePending]
  · intro r noise outside
    exact (head.native r noise (fun n hn => outside n (List.mem_append_left _ hn))).trans
      (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn)))

/-- Exact-size allocator route to the young-child tail loop. -/
theorem single_fresh_young {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : YoungSingleConditions R (allocatedPayload R c) childDomain
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (YoungSingleResult R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh input allocation).run
  intro middle allocated
  exact (allocated.toResult.single_young conditions).run middle ⟨allocated.pc,rfl⟩

/-- Least-large-block allocator route to the young-child tail loop. -/
theorem single_fresh_large_young {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : YoungSingleConditions R (largePayload R c) childDomain
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (YoungSingleResult R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh_large input allocation).run
  intro middle allocated
  exact (allocated.single_young conditions).run middle ⟨allocated.pc,rfl⟩

/-- The captured child remains represented under the original placement.
In particular, a self-pointer cannot yet use the parent's new address. -/
theorem YoungSingleResult.captured {R target log before after pl cp tag value}
    (post : YoungSingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8) :
    (Reloc.Eqv.valRead value (fun c => gprGet c.σ 8)).P pl 0 after := by
  refine ⟨word before (R 10).toNat,?_,?_⟩
  · exact post.value.trans (congrArg some (single_child_original allocationOutside rootOutside))
  · simpa using object.2 0 value rfl

end OCaml.Vm.Gc.Fresh
