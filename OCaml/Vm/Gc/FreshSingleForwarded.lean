import OCaml.Vm.Gc.FreshSingleYoung
import OCaml.Vm.Gc.SingleFieldForwardedReturn

namespace OCaml.Vm.Gc.SingleField
open Vsa.Machine Vsa.Sim Primitives

theorem forwardedValue_of_memory {q root before after} (memory : after.σ.mem = before.σ.mem) :
    forwardedValue q root after = forwardedValue q root before := by
  simp only [forwardedValue,word,forwardedSnapshot_memory memory,child_of_memory memory]

theorem forwardedEffect_of_memory {q root before after} (memory : after.σ.mem = before.σ.mem) :
    forwardedEffect q root after = forwardedEffect q root before := by
  simp only [forwardedEffect,forwardedValue_of_memory memory]

theorem ForwardedReturnConditions.of_memory {q root sp before after}
    (memory : after.σ.mem = before.σ.mem) (conditions : ForwardedReturnConditions q root sp before) :
    ForwardedReturnConditions q root sp after := by
  have same := forwardedSnapshot_memory (q := q) (root := root) memory
  refine {
    header := ?_
    headerRead := ?_
    pointerRead := ?_
    rootWrite := conditions.rootWrite
    windows := conditions.windows
    outside := ?_
    aligned := ?_
    prefixOutside := conditions.prefixOutside }
  · simpa only [word,same,child_of_memory memory] using conditions.header
  · simpa only [child_of_memory memory] using conditions.headerRead
  · simpa only [child_of_memory memory] using conditions.pointerRead
  · simpa only [word,same,child_of_memory memory] using conditions.outside
  · simpa only [OldifyReturn.returnWord,word,same] using conditions.aligned

end OCaml.Vm.Gc.SingleField

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Both allocation alternatives share the same data-only child forwarding
and native-frame premises. The allocator's save-bank separation is explicit. -/
structure ForwardedSingleConditions (R : Nat → BitVec 64) (target domain : BitVec 64)
    (log : List WEntry) (c : Config) : Prop extends YoungSingleConditions R target domain log c where
  returns : SingleField.ForwardedReturnConditions (queuePending R target) (R 11)
    (OldifyEntry.frameSp R) (queueSnapshot R log c)
  allocationOutside : ∀ cell ∈ OldifyEntry.saves,
    OutLRange log (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat 8

structure ForwardedSingleResult (R : Nat → BitVec 64) (target : BitVec 64) (log : List WEntry)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt (R 1) after
  registers : GHolds after.σ (OldifyEntry.callerRegs R)
  memory : after.σ.mem = writeLog before.σ.mem ((OldifyEntry.saveLog OldifyEntry.saves R ++ log) ++
    SingleField.forwardedEffect (queuePending R target) (R 11) (queueSnapshot R log before))
  value : word after target.toNat =
    SingleField.forwardedValue (queuePending R target) (R 11) (queueSnapshot R log before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ ((wrChain Forwarded.blocks ++ wrChain OldifyReturn.blocks) ++ [8,9,14,15,25]) ++
      ((1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15]), (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Complete forwarded-child return after either actual allocator, with the
original caller bank identified from the real saved words. -/
theorem AllocationResult.single_forwarded {R target domain log c middle}
    (allocated : AllocationResult R target log c middle) (input : OldifyEntry.Input R c)
    (conditions : ForwardedSingleConditions R target domain log c) :
    FnSummary Enqueue.pc (fun d => d = middle) (ForwardedSingleResult R target log c) := by
  constructor
  intro start pre
  rcases pre with ⟨_,equal⟩
  subst start
  have memory : middle.σ.mem = (queueSnapshot R log c).σ.mem := by
    simpa only [queueSnapshot] using allocated.memory
  have childInput : SingleField.Input (queuePending R target) (R 11) middle :=
    allocated.single_prefix_input conditions.single conditions.prefixWindows
  have even : ChildClassify.even (SingleField.child (queuePending R target) (R 11) middle) = true := by
    simpa only [SingleField.child_of_memory memory] using conditions.even
  obtain ⟨after,run,returned⟩ := (SingleField.return_young_forwarded childInput
    allocated.stack allocated.constants even (conditions.range.of_memory memory)
    (conditions.returns.of_memory memory)).run middle ⟨allocated.pc,rfl⟩
  have saved := allocated.saved input conditions.allocationOutside
  have returnWord : OldifyReturn.returnWord (OldifyEntry.frameSp R) middle = R 1 :=
    saved OldifyReturn.slots.head! (by decide)
  refine ⟨after,run,⟨returned.good,returned.tick,returned.minstret,returned.code,?_,?_,?_,?_,
    returned.output.trans allocated.output,?_⟩⟩
  · simpa only [returnWord] using returned.pc
  · simpa only [OldifyEntry.restored_of_saved saved] using returned.registers
  · rw [returned.memory,SingleField.forwardedEffect_of_memory memory,allocated.memory]
    simp only [writeLog_append]
  · simpa only [SingleField.forwardedValue_of_memory memory,queuePending] using returned.value
  · intro r noise outside
    exact (returned.native r noise (fun n hn => outside n (List.mem_append_left _ hn))).trans
      (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn)))

/-- Whole oldify call through exact-size allocation and a forwarded young child. -/
theorem single_fresh_forwarded {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : AllocationConditions R c)
    (conditions : ForwardedSingleConditions R (allocatedPayload R c) childDomain
      (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (ForwardedSingleResult R (allocatedPayload R c) (AllocWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh input allocation).run
  intro middle allocated
  exact (allocated.toResult.single_forwarded input.entry conditions).run middle ⟨allocated.pc,rfl⟩

/-- Whole oldify call through least-large-block allocation and a forwarded young child. -/
theorem single_fresh_large_forwarded {R domain size tag childDomain c} (input : EntryInput R domain size tag c)
    (allocation : LargeAllocationConditions R c)
    (conditions : ForwardedSingleConditions R (largePayload R c) childDomain
      (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) :
    FnSummary OldifyEntry.pc (fun d => d = c)
      (ForwardedSingleResult R (largePayload R c) (AllocLargeWrapper.effect (allocatorRegs R c) (oldifySnapshot R c)) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (allocate_fresh_large input allocation).run
  intro middle allocated
  exact (allocated.single_forwarded input.entry conditions).run middle ⟨allocated.pc,rfl⟩

/-- Whole-call typed relocation follows from the original object and the
partial relocation's forwarding word, despite allocation and forwarding
having overwritten the original field in the machine memory. -/
theorem ForwardedSingleResult.payload {R target log before after pl cp tag value μ}
    (post : ForwardedSingleResult R target log before after)
    (object : ObjAt before pl cp (R 10).toNat (.block tag [value]))
    (allocationOutside : OutLRange (OldifyEntry.saveLog OldifyEntry.saves R ++ log) (R 10).toNat 8)
    (rootOutside : OutLRange [((R 11).toNat,8,target)] (R 10).toNat 8)
    (forwarding : SingleField.forwardedValue (queuePending R target) (R 11) (queueSnapshot R log before) =
      Reloc.relocWord μ pl value (SingleField.child (queuePending R target) (R 11) (queueSnapshot R log before))) :
    (Reloc.Eqv.val value id).P (Reloc.reloc μ pl) target.toNat after := by
  apply single_field_relocated object
  rw [post.value,forwarding,single_child_original allocationOutside rootOutside]

end OCaml.Vm.Gc.Fresh
