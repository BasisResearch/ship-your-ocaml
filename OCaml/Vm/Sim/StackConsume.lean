import OCaml.Vm.Sim.StackDrop
import OCaml.Vm.Sim.ReadOnly

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- A consuming arm retains environment, extra arguments and loop registers. -/
def consumePreserved : List Register :=
  [gprReg Layout.reg_env, gprReg Layout.reg_extra,
   gprReg Layout.reg_dispatchTable, gprReg Layout.reg_opcodeBound,
   gprReg Layout.reg_pending, gprReg Layout.reg_domain]

/-- Register/output observations with an exact, opaque memory effect. -/
structure StackPost (before : Config) (pl : Place) (pc sp : Nat) (w : BitVec 64)
    (memoryAfter : Std.ExtHashMap Nat (BitVec 8)) (after : Config) : Prop where
  good : GoodState after.σ
  head : pcOf after = some (BitVec.ofNat 64 Layout.loopHead)
  code : gpr after Layout.reg_pc = some (BitVec.ofNat 64 (pl.codeBase + 4 * pc))
  stack : gpr after Layout.reg_sp = some (BitVec.ofNat 64 sp)
  accu : gpr after Layout.reg_accu = some w
  memory : after.σ.mem = memoryAfter
  output : after.σ.sailOutput = before.σ.sailOutput
  preserved : ∀ r ∈ consumePreserved, after.σ.regs.get? r = before.σ.regs.get? r

/-- Read-only specialization for stack-consuming bodies. -/
abbrev ConsumeValuePost (before : Config) (pl : Place) (pc sp : Nat) (w : BitVec 64)
    (after : Config) : Prop := StackPost before pl pc sp w before.σ.mem after

/-- Integer-result specialization retained for the arithmetic families. -/
abbrev ConsumePost (before : Config) (pl : Place) (pc sp : Nat) (n : BitVec 63)
    (after : Config) : Prop := ConsumeValuePost before pl pc sp (tag64 n) after

/-- Retain the result as a root before dropping its source stack slots. -/
theorem consume_value_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc count : Nat} {v : Val} {w : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (value : valWord pl v = some w)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (bound : count ≤ s.stack.length)
    (post : ConsumeValuePost c pl pc (sp + 8 * count) w after) :
    Running L P {s with pc := pc, accu := v, stack := s.stack.drop count} after := by
  have payload := payload_pc (payload_stack_drop ((payload_of_repr data).accu_of_root v root) bound) pc
  apply readOnly_restore stable payload data.primitives platform ?_ ?_
    post.good post.memory post.output
  · refine ⟨post.head, post.code, post.stack, ⟨w, post.accu, value⟩, ?_, ?_⟩
    · obtain ⟨w, hw, hv⟩ := data.env
      exact ⟨w, (post.preserved _ (by decide)).trans hw, hv⟩
    · exact (post.preserved _ (by decide)).trans data.extra
  · exact ⟨(post.preserved _ (by decide)).trans loop.dispatchTable,
      (post.preserved _ (by decide)).trans loop.opcodeBound,
      (post.preserved _ (by decide)).trans loop.pending,
      (post.preserved _ (by decide)).trans loop.domain⟩

/-- Compose dispatch with a generated consuming body, sharing payload restoration. -/
theorem consume_value_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high pc count : Nat} {v : Val} {w : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s op c pl cp sp high)
    (value : valWord pl v = some w)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (bound : count ≤ s.stack.length)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧ ConsumeValuePost d pl pc (sp + 8 * count) w after) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := pc, accu := v, stack := s.stack.drop count} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nb, after, hb, post⟩ := body d dp
  refine ⟨nb, after, hb, ?_⟩
  apply consume_value_restore stable h.toVmReprAt h.running.platform h.dispatch.loop value root bound
  exact ⟨post.good, post.head, post.code, post.stack, post.accu,
      post.memory.trans dp.memory, post.output.trans dp.frame.out,
      fun r hr => (post.preserved r hr).trans
        (dp.frame.frame r (by revert r; decide))⟩

/-- Existing integer restoration API, obtained from the arbitrary-result rule. -/
theorem consume_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc count : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (data : VmReprAt P s c pl cp sp high)
    (platform : PlatformOk L.runtimeOk c) (loop : LoopRegisters c)
    (bound : count ≤ s.stack.length)
    (post : ConsumePost c pl pc (sp + 8 * count) n after) :
    Running L P {s with pc := pc, accu := .int n, stack := s.stack.drop count} after :=
  consume_value_restore stable data platform loop rfl (fun _ hl => by cases hl) bound post

/-- Integer binary arms share the general consuming composition. -/
theorem consume_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode}
    {c : Config} {pl : Place} {cp : ChanPlace} {sp high pc count : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s op c pl cp sp high)
    (bound : count ≤ s.stack.length)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧ ConsumePost d pl pc (sp + 8 * count) n after) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := pc, accu := .int n, stack := s.stack.drop count} after :=
  consume_value_arm stable h rfl (fun _ hl => by cases hl) bound body

end OCaml.Vm.Sim
