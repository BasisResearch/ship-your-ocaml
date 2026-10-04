import OCaml.Vm.Gc.AllocationContext
import OCaml.Vm.Gc.AllocWrapperCore
import OCaml.Vm.Gc.Generated.Enqueue

namespace OCaml.Vm.Gc.Fresh
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Common result of either proved allocation route at fresh oldify's queue
entry. Payload and write log are parameters supplied by the selected route. -/
structure AllocationResult (R : Nat → BitVec 64) (payload : BitVec 64) (log : List WEntry)
    (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  pc : PCAt Enqueue.pc after
  registers : GHolds after.σ (Enqueue.regs (R 10) payload (R 11)
    (sizeWord (word before (R 10 - 8#64).toNat)))
  stack : gprGet after.σ 2 = some (OldifyEntry.frameSp R)
  constants : GHolds after.σ loopConstants
  memory : after.σ.mem = writeLog before.σ.mem
    (OldifyEntry.saveLog OldifyEntry.saves R ++ log)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ (1 :: prepareWrites) ++ [1,2,8,9,10,11,12,13,14,15], (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem AllocationResult.domainRegister {R payload log before after}
    (post : AllocationResult R payload log before after) :
    gprGet after.σ 18 = some (BitVec.ofNat 64 Layout.sym_Caml_state) :=
  gholds_lookup _ post.constants rfl

/-- Compose the proved fresh prefix with a proved wrapper return. This
shares oldify register preservation and exact memory composition across
allocator routes, without postulating execution of either route. -/
theorem AllocationEntry.finish {R hp log before middle after}
    (entered : AllocationEntry R before middle)
    (allocated : AllocWrapperCore.Post (allocatorRegs R before) hp log middle after)
    (high : ∀ e ∈ AllocWrapperCore.effect (allocatorRegs R before) hp log middle,
      Layout.sym_tohost + 16 ≤ e.1) :
    AllocationResult R (hp + BitVec.ofNat 64 Layout.header_bytes)
      (AllocWrapperCore.effect (allocatorRegs R before) hp log middle) before after := by
  have done := entered.context.finish allocated ⟨rfl,rfl,rfl,rfl⟩ high
  refine ⟨done.good,done.minstret,done.tick,done.code,done.pc,done.registers,
    done.stack,done.constants,?_,done.output.trans entered.output,?_⟩
  · rw [done.memory,entered.memory,writeLog_append]
  · intro r noise outside
    exact (done.native r noise (fun n hn => outside n (List.mem_append_right _ hn))).trans
      (entered.native r noise (fun n hn => outside n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.Fresh
