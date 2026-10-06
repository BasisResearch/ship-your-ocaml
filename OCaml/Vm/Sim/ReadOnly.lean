import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.InvariantUse

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Fixed loop registers, independent of the current opcode's data registers. -/
def loopPreserved : List Register :=
  [gprReg Layout.reg_dispatchTable, gprReg Layout.reg_opcodeBound,
   gprReg Layout.reg_pending, gprReg Layout.reg_domain, Register.htif_payload_writes]

/-- Reconstruct all fixed loop registers from one finite frame check. -/
theorem loopRegisters_frame {before after : Config}
    (frame : ∀ r ∈ loopPreserved, after.σ.regs.get? r = before.σ.regs.get? r)
    (loop : LoopRegisters before) : LoopRegisters after :=
  ⟨(frame _ (by decide)).trans loop.dispatchTable,
   (frame _ (by decide)).trans loop.opcodeBound,
   (frame _ (by decide)).trans loop.pending,
   (frame _ (by decide)).trans loop.domain,
   (frame _ (by decide)).trans loop.htifIdle⟩

/-- Register observations common to all read-only arm results. Memory payload
and platform preservation are separate so stack-consuming arms can reuse them. -/
structure VmRegisters (s : St) (pl : Place) (sp : Nat) (c : Config) : Prop where
  head : pcOf c = some (BitVec.ofNat 64 Layout.loopHead)
  pc : gpr c Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
  spReg : gpr c Layout.reg_sp = some (BitVec.ofNat 64 sp)
  accu : ∃ w, gpr c Layout.reg_accu = some w ∧ valWord pl s.accu = some w
  env : ∃ w, gpr c Layout.reg_env = some w ∧ valWord pl s.env = some w
  extra : gpr c Layout.reg_extra = some (BitVec.ofNat 64 s.extra)

/-- Assemble the loop relation once all named data/platform/register parts
are established, independently of the arm's memory effect. -/
theorem running_of_payload {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (data : VmPayload P s c pl cp sp high) (primitives : PrimitiveBindings P c)
    (platform : PlatformOk L.runtimeOk c) (regs : VmRegisters s pl sp c)
    (loop : LoopRegisters c) (geometry : OCaml.LoopGeometry L P s c pl cp high)
    (native : NativePlaced c) : Running L P s c := by
  have repr : VmReprAt P s c pl cp sp high := ⟨regs.head, regs.pc, regs.spReg, regs.accu, regs.env, regs.extra,
    data.stackHigh, data.trapsp, data.codeBase, data.code,
    data.globals, data.stack, data.heap, data.world, primitives, data.atomBase⟩
  exact ⟨⟨pl, cp, sp, high, repr⟩, platform, loop, ⟨pl, cp, sp, high, repr, geometry⟩, native⟩

/-- Restore any read-only result once its payload and register observations
are established. This is the common image/runtime/primitive-table frame. -/
theorem readOnly_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk) (payload : VmPayload P s c pl cp sp high)
    (primitives : PrimitiveBindings P c) (platform : PlatformOk L.runtimeOk c)
    (regs : VmRegisters s pl sp after) (loop : LoopRegisters after)
    (good : GoodState after.σ) (memory : after.σ.mem = c.σ.mem)
    (output : after.σ.sailOutput = c.σ.sailOutput)
    (geometry : OCaml.LoopGeometry L P s c pl cp high) (native : NativePlaced c)
    (nativeSp : gpr after 2 = gpr c 2) : Running L P s after := by
  apply running_of_payload (payload.frame memory output) (primitives.frame memory) ?_ regs loop
    (geometry.same rfl rfl memory) (native.frame_read memory nativeSp)
  exact ⟨good,
    ⟨fun i hi => by rw [memory]; exact platform.image.text i hi,
     fun i hi => by rw [memory]; exact platform.image.rodata i hi⟩,
    stable c after memory platform.runtime⟩

end OCaml.Vm.Sim
