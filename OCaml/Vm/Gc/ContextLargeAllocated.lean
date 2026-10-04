import OCaml.Vm.Gc.ContextAllocated
import OCaml.Vm.Gc.AllocLargeWrapper

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Least-large-block allocation geometry in the current tail state. -/
structure ContextLargeConditions (R : Nat → BitVec 64) (c : Config) : Prop where
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  freeCode : Code.Bf_allocateLoaded c.σ.mem
  ffsCode : Code.FfsLoaded c.σ.mem
  splitCode : Code.Bf_splitLoaded c.σ.mem
  windows : AllocEntry.Windows R
  pointer : word c Layout.sym_caml_fl_p_allocate = BestFitSmall.pc
  inner : OutLRange (AllocEntry.prefixLog R) Layout.sym_caml_fl_p_allocate 8
  wrapper : AllocLargeWrapper.Conditions R c

theorem ContextLargeConditions.of_memory {R} {before after : Config} (memory : after.σ.mem = before.σ.mem)
    (conditions : ContextLargeConditions R before) : ContextLargeConditions R after :=
  ⟨memory ▸ conditions.code,memory ▸ conditions.freeCode,memory ▸ conditions.ffsCode,
    memory ▸ conditions.splitCode,conditions.windows,
    by simpa only [word,memory] using conditions.pointer,conditions.inner,conditions.wrapper.of_memory memory⟩

def contextLargePayload (source root sp hd : BitVec 64) (c : Config) : BitVec 64 :=
  AllocLargeWrapper.resultHeader (contextRegs source root sp hd) c + BitVec.ofNat 64 Layout.header_bytes

theorem contextLargePayload_of_memory {source root sp hd} {before after : Config} (memory : after.σ.mem = before.σ.mem) :
    contextLargePayload source root sp hd after = contextLargePayload source root sp hd before := by
  simp only [contextLargePayload,AllocLargeWrapper.resultHeader_of_memory memory]

/-- Actual fresh tail entry through the empty-small-list, zero-bitmap,
least-large-block split alternative, retaining the current native frame. -/
theorem allocate_context_large {source root sp c} (input : Input source c)
    (carried : GHolds c.σ (contextCarried sp root))
    (conditions : ContextLargeConditions (contextRegs source root sp (word c (source - 8#64).toNat)) c) :
    FnSummary pc (fun d => d = c)
      (fun after => ContextAllocated source root sp (word c (source - 8#64).toNat)
        (contextLargePayload source root sp (word c (source - 8#64).toNat) c)
        (AllocLargeWrapper.effect (contextRegs source root sp (word c (source - 8#64).toNat)) c) c after
        ((1 :: wrChain blocks) ++ [1,2,8,9,10,11,12,13,14,15])) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare_context input carried).run
  intro middle entered
  let R := contextRegs source root sp (word c (source - 8#64).toNat)
  have allocInput : AllocLargeWrapper.Input R middle :=
    { toInput := entered.context.wrapper_input (entered.memory ▸ conditions.code) conditions.windows
        (by simpa only [word,entered.memory] using conditions.pointer) conditions.inner
      toConditions := conditions.wrapper.of_memory entered.memory
      freeCode := entered.memory ▸ conditions.freeCode
      ffsCode := entered.memory ▸ conditions.ffsCode
      splitCode := entered.memory ▸ conditions.splitCode }
  obtain ⟨after,run,allocated⟩ := (AllocLargeWrapper.allocate allocInput).run middle ⟨entered.pc,rfl⟩
  have done := entered.context.finish allocated ⟨rfl,rfl,rfl,rfl⟩
    (AllocLargeWrapper.effect_high conditions.windows allocInput.toConditions)
  change ContextAllocated _ _ _ _ (_ + _) (AllocLargeWrapper.effect R middle) middle after at done
  rw [AllocLargeWrapper.effect_of_memory entered.memory,AllocLargeWrapper.resultHeader_of_memory entered.memory] at done
  exact ⟨after,run,entered.complete done⟩

end OCaml.Vm.Gc.Fresh
