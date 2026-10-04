import OCaml.Vm.Gc.FreshAllocator
import OCaml.Vm.Gc.AllocWrapperCore
import OCaml.Vm.Gc.Generated.Enqueue

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Loop state retained across allocation, independent of the original
native caller and of how many tail children have already been forwarded. -/
def contextCarried (sp root : BitVec 64) : GRegs := [(2,sp),(9,root)] ++ loopConstants

/-- The allocation-call interface shared by native entry and tail entry.
The original saved bank is intentionally outside this local interface. -/
structure AllocationContext (source root sp hd : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  arguments : GHolds c.σ (Fresh.arguments source hd)
  carried : GHolds c.σ (contextCarried sp root)
  link : gprGet c.σ 1 = some call.link

/-- Only these six incoming registers are read by the allocator wrapper. -/
def contextRegs (source root sp hd : BitVec 64) (n : Nat) : BitVec 64 :=
  if n = 1 then call.link else if n = 2 then sp else if n = 8 then source
  else if n = 9 then root else if n = 10 then sizeWord hd
  else if n = 11 then tagWord hd else 0

theorem AllocationEntry.context {R before after} (post : AllocationEntry R before after) :
    AllocationContext (R 10) (R 11) (OldifyEntry.frameSp R)
      (word before (R 10 - 8#64).toNat) after :=
  ⟨post.good,post.minstret,post.tick,post.code,post.arguments,post.carried,post.link⟩

/-- Proved header preparation supplies the local call interface after the
actual JAL. The finite pin list contains all tag constants needed by tail iterations. -/
structure ContextEntered (source root sp hd : BitVec 64) (before after : Config) : Prop where
  context : AllocationContext source root sp hd after
  pc : PCAt allocationPc after
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ 1 :: wrChain blocks, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Allocation prefix starting at the loop's header classifier. It neither
saves a new oldify frame nor assumes an allocation execution. -/
theorem prepare_context {source root sp c} (input : Input source c)
    (carried : GHolds c.σ (contextCarried sp root)) :
    FnSummary pc (fun d => d = c)
      (ContextEntered source root sp (word c (source - 8#64).toNat) c) := by
  constructor
  apply Vsa.Logic.Triple.seq (prepare input).run
  intro middle prepared
  have kept : GHolds middle.σ (contextCarried sp root) := by
    apply gholds_of_frame (prepared.machine.frame_subset written) _
      (by change KeysOK [2,9,18,19,20,21,22,23]; decide) ?_ ?_ carried
    · change ∀ n ∈ [2,9,18,19,20,21,22,23], ∀ q ∈ noiseRegs, (q == gprReg n) = false
      decide
    · change ∀ n ∈ [2,9,18,19,20,21,22,23], ∀ m ∈ [10,11,12,24,25], (gprReg m == gprReg n) = false
      decide
  let pins := Fresh.arguments source (word c (source - 8#64).toNat) ++ contextCarried sp root
  have holds : GHolds middle.σ pins := (gholds_append _ _).mpr ⟨prepared.registers,kept⟩
  have summary := call_summary call_shape call_decode middle (call_pins prepared.code)
    prepared.machine.good prepared.machine.tick prepared.machine.minstret pins holds
    (by change KeysOK [10,25,11,24,12,8,19,2,9,18,19,20,21,22,23]; decide)
    (by change ∀ n ∈ [10,25,11,24,12,8,19,2,9,18,19,20,21,22,23], n ≠ 1; decide)
  obtain ⟨after,run,called⟩ := summary.run middle ⟨prepared.pc,rfl⟩
  have split := (gholds_append _ _).mp called.registers
  refine ⟨after,run,⟨⟨called.good,called.minstret,called.tick,called.mem ▸ prepared.code,
    split.1,split.2,called.ra⟩,?_,called.mem.trans prepared.memory,
    called.output.trans prepared.machine.output,?_⟩⟩
  · simpa only [PCAt,call_target] using called.pc
  · intro r noise outside
    exact (called.frame r noise (by simp [wrChain]) (outside 1 (List.mem_cons_self ..))).trans
      (prepared.machine.frame r noise (fun n hn => outside n (List.mem_cons_of_mem _ hn)))

/-- The shared finite call interface gives the wrapper's concrete inputs. -/
theorem AllocationContext.wrapper_input {source root sp hd c}
    (context : AllocationContext source root sp hd c)
    (code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem)
    (windows : AllocEntry.Windows (contextRegs source root sp hd))
    (pointer : word c Layout.sym_caml_fl_p_allocate = BestFitSmall.pc)
    (outside : OutLRange (AllocEntry.prefixLog (contextRegs source root sp hd)) Layout.sym_caml_fl_p_allocate 8) :
    AllocEntry.Input (contextRegs source root sp hd) BestFitSmall.pc c := by
  refine ⟨context.good,context.minstret,context.tick,code,?_,windows,?_,pointer,outside⟩
  · exact ⟨gholds_lookup _ context.carried rfl,context.link,gholds_lookup _ context.arguments rfl,
      gholds_lookup _ context.carried rfl,gholds_lookup _ context.arguments rfl,
      gholds_lookup _ context.arguments rfl,True.intro⟩
  · change (sizeWord hd).toNat ≤ AllocEntry.maximum.toNat
    rw [sizeWord_nat]
    have bound := hd.isLt
    change _ ≤ 18014398509481983
    omega

/-- Common post-allocation interface for both first-entry and tail-entry
calls. The log starts at the current allocation call, not at a native prologue. -/
structure ContextAllocated (source root sp hd payload : BitVec 64) (log : List WEntry)
    (before after : Config) (writes : List Nat := [1,2,8,9,10,11,12,13,14,15]) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt Enqueue.pc after
  registers : GHolds after.σ (Enqueue.regs source payload root (sizeWord hd))
  stack : gprGet after.σ 2 = some sp
  constants : GHolds after.σ loopConstants
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ writes, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

/-- Shared allocation-return frame and oldify-code preservation. The four
caller-map equalities connect the wrapper's saved registers with the loop. -/
theorem AllocationContext.finish {source root sp hd R hp log before after}
    (context : AllocationContext source root sp hd before)
    (allocated : AllocWrapperCore.Post R hp log before after)
    (caller : R 1 = call.link ∧ R 2 = sp ∧ R 8 = source ∧ R 9 = root)
    (high : ∀ e ∈ AllocWrapperCore.effect R hp log before, Layout.sym_tohost + 16 ≤ e.1) :
    ContextAllocated source root sp hd (hp + BitVec.ofNat 64 Layout.header_bytes)
      (AllocWrapperCore.effect R hp log before) before after := by
  have kept : GHolds after.σ ([(24,source - 8#64),(25,sizeWord hd)] ++ loopConstants) := by
    apply gholds_of_frame allocated.native _ (by change KeysOK [24,25,18,19,20,21,22,23]; decide)
      (by change ∀ n ∈ [24,25,18,19,20,21,22,23], ∀ q ∈ noiseRegs, (q == gprReg n) = false; decide)
      (by change ∀ n ∈ [24,25,18,19,20,21,22,23], ∀ m ∈ [1,2,8,9,10,11,12,13,14,15],
          (gprReg m == gprReg n) = false; decide)
    exact (gholds_append _ _).mpr ⟨⟨gholds_lookup _ context.arguments rfl,
      gholds_lookup _ context.arguments rfl,True.intro⟩,((gholds_append _ _).mp context.carried).2⟩
  have stack : gprGet after.σ 2 = some (R 2) := gholds_lookup _ allocated.registers rfl
  have sourcePin : gprGet after.σ 8 = some (R 8) := gholds_lookup _ allocated.registers rfl
  have rootPin : gprGet after.σ 9 = some (R 9) := gholds_lookup _ allocated.registers rfl
  refine ⟨allocated.good,allocated.minstret,allocated.tick,?_,?_,?_,?_,
    ((gholds_append _ _).mp kept).2,allocated.memory,allocated.output,allocated.native⟩
  · rw [allocated.memory]
    apply image_writeLog Code.caml_oldify_one_transport context.code
    intro e member
    exact Nat.le_trans (by decide) (high e member)
  · have link : call.link = Enqueue.pc := by decide
    simpa only [caller.1,link] using allocated.pc
  · exact ⟨allocated.result,by simpa only [caller.2.2.2] using rootPin,
      by simpa only [caller.2.2.1] using sourcePin,gholds_lookup _ kept rfl,
      gholds_lookup _ kept rfl,gholds_lookup _ kept rfl,True.intro⟩
  · simpa only [caller.2.1] using stack

/-- Compose the read-only classifier/JAL prefix with any proved allocation
result. The exact write log remains that of the allocator alone. -/
theorem ContextEntered.complete {source root sp hd payload log writes before middle after}
    (entered : ContextEntered source root sp hd before middle)
    (allocated : ContextAllocated source root sp hd payload log middle after writes) :
    ContextAllocated source root sp hd payload log before after ((1 :: wrChain blocks) ++ writes) := by
  refine ⟨allocated.good,allocated.minstret,allocated.tick,allocated.code,allocated.pc,
    allocated.registers,allocated.stack,allocated.constants,?_,allocated.output.trans entered.output,?_⟩
  · simpa only [entered.memory] using allocated.memory
  · intro r noise outside
    exact (allocated.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (entered.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.Fresh
