import OCaml.Vm.Gc.AllocationContext
import OCaml.Vm.Gc.AllocationFootprint

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Exact free-list allocation conditions at the current tail boundary.
All observations refer to the existing frame and current memory. -/
structure ContextAllocationConditions (R : Nat → BitVec 64) (c : Config) : Prop where
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  windows : AllocEntry.Windows R
  pointer : word c Layout.sym_caml_fl_p_allocate = BestFitSmall.pc
  inner : OutLRange (AllocEntry.prefixLog R) Layout.sym_caml_fl_p_allocate 8
  wrapper : AllocWrapper.Conditions R c

def contextPayload (source root sp hd : BitVec 64) (c : Config) : BitVec 64 :=
  BestFitSmall.first (sizeWord hd) (AllocWrapper.prepared (contextRegs source root sp hd) c)

/-- Fresh header classification, actual allocation JAL and complete exact-size
allocation on the existing native frame. This is the fresh-child tail route. -/
theorem allocate_context {source root sp c} (input : Input source c)
    (carried : GHolds c.σ (contextCarried sp root))
    (conditions : ContextAllocationConditions (contextRegs source root sp (word c (source - 8#64).toNat)) c) :
    FnSummary pc (fun d => d = c)
      (fun after => ContextAllocated source root sp (word c (source - 8#64).toNat)
        (contextPayload source root sp (word c (source - 8#64).toNat) c)
        (AllocWrapper.effect (contextRegs source root sp (word c (source - 8#64).toNat)) c) c after
        ((1 :: wrChain blocks) ++ [1,2,8,9,10,11,12,13,14,15])) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_context input carried).run
  intro middle entered
  let R := contextRegs source root sp (word c (source - 8#64).toNat)
  have allocInput : AllocWrapper.Input R middle :=
    { toInput := entered.context.wrapper_input (entered.memory ▸ conditions.code) conditions.windows
        (by simpa only [word,entered.memory] using conditions.pointer) conditions.inner
      toConditions := conditions.wrapper.of_memory entered.memory
      freeListCode := entered.memory ▸ conditions.freeCode }
  obtain ⟨after,run,allocated⟩ := (AllocWrapper.allocate allocInput).run middle ⟨entered.pc,rfl⟩
  have high : ∀ e ∈ AllocWrapperCore.effect R
      (AllocExact.resultHeader (R 10) (AllocWrapper.prepared R middle))
      (BestFitExact.effect (R 10) (AllocWrapper.prepared R middle)) middle,
      Layout.sym_tohost + 16 ≤ e.1 := by
    rw [← AllocWrapper.effect_eq_core]
    exact AllocWrapper.effect_high conditions.windows allocInput.toConditions
  have done := entered.context.finish allocated.toCore ⟨rfl,rfl,rfl,rfl⟩ high
  rw [← AllocWrapper.effect_eq_core,AllocWrapper.effect_of_memory entered.memory] at done
  have payload : BestFitSmall.first (R 10) (AllocWrapper.prepared R middle) =
      contextPayload source root sp (word c (source - 8#64).toNat) c := by
    simp only [contextPayload,BestFitSmall.first,word,AllocWrapper.prepared_memory entered.memory]
    rfl
  have result : ContextAllocated source root sp (word c (source - 8#64).toNat)
      (contextPayload source root sp (word c (source - 8#64).toNat) c)
      (AllocWrapper.effect R c) middle after := by
    simpa only [AllocExact.resultHeader,BitVec.sub_add_cancel,payload] using done
  exact ⟨after,run,entered.complete result⟩

end OCaml.Vm.Gc.Fresh
