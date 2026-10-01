import OCaml.Vm.Sim.ArmInput

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Register observations common to all read-only arm results. Memory payload
and platform preservation are separate so stack-consuming arms can reuse them. -/
structure VmRegisters (s : St) (pl : Place) (sp : Nat) (c : Config) : Prop where
  head : pcOf c = some (BitVec.ofNat 64 Layout.loopHead)
  pc : gpr c Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
  spReg : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  accu : ∃ w, gpr c Layout.reg_accu = some w ∧ valWord pl s.accu = some w
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)

/-- Restore any read-only result once its payload and register observations
are established. This is the common image/runtime/primitive-table frame. -/
theorem readOnly_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk) (payload : VmPayload P s c pl cp sp high)
    (primitives : PrimitiveBindings P c) (platform : PlatformOk L.runtimeOk c)
    (regs : VmRegisters s pl sp after) (loop : LoopRegisters after)
    (good : GoodState after.σ) (memory : after.σ.mem = c.σ.mem)
    (output : after.σ.sailOutput = c.σ.sailOutput) : Running L P s after := by
  have data := payload.frame memory output
  refine ⟨⟨pl, cp, sp, high, ?_⟩, ?_, loop⟩
  · exact ⟨regs.head, regs.pc, regs.spReg, regs.accu, regs.env, regs.extra,
      data.stackHigh, data.trapsp, data.codeBase, data.code,
      data.globals, data.stack, data.heap, data.world, primitives.frame memory⟩
  · exact ⟨good,
      ⟨fun i hi => by rw [memory]; exact platform.image.text i hi,
       fun i hi => by rw [memory]; exact platform.image.rodata i hi⟩,
      stable c after memory platform.runtime⟩

end OCaml.Vm.Sim
