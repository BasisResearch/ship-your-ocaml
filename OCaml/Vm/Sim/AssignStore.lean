import OCaml.Vm.Sim.StackEdit

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Static write window and separation for one represented stack assignment. -/
structure AssignWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high i : Nat) (w : BitVec 64) : Prop where
  window : WriteWindow (BitVec.ofNat 64 (sp + 8 * i)) 8
  payload : StackEditOutside (assignLog sp i w) P s c pl cp high
  image : ImageOutside (assignLog sp i w)
  young : YoungOutside (assignLog sp i w) c
  bindings : BindingsOutside (assignLog sp i w) P c

/-- Restore the exact represented stack edit and the unit accumulator. -/
theorem assign_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high i pc : Nat} {w : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp + 8 * i, sp + 8 * i + 8⟩])
    (data : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (space : AssignWriteOk P s c pl cp sp high i w)
    (bound : i < s.stack.length) (value : valWord pl s.accu = some w)
    (post : StackPost c pl pc sp (tag64 0) (writeLog c.σ.mem (assignLog sp i w)) after)
    (geometry : ArmGeometry P s c pl cp high)
    (native : NativePlaced c) :
    Running L P {s with pc := pc, accu := .unit, stack := s.stack.set i s.accu} after := by
  have payload := payload_stack_assign (payload_of_repr data) bound value space.payload post.memory post.output
  have selected := payload.accu_int 0
  have memoryFrame : FrameOn [⟨sp + 8 * i, sp + 8 * i + 8⟩] c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [assignLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact running_of_payload (payload_pc selected pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable c after memoryFrame platform.runtime⟩
    (post.registers data rfl rfl rfl) (post.loopRegisters loop)
    (geometry.frame_log rfl rfl space.payload.core.domain space.bindings.contents space.young post.memory)
    (native.frame_vm (ws := [⟨sp + 8 * i, sp + 8 * i + 8⟩]) (by simp only [assignLog, LogInW, InsideW, or_false, and_true]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩) (by simp only [List.mem_singleton, forall_eq]; exact geometry.stack_below (by have := data.stack.1; omega)) space.payload.core.domain post.memory post.nativeSp)

/-- Compose dispatch and a generated stack-assignment body. -/
theorem assign_body_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high i pc : Nat} {w : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp + 8 * i, sp + 8 * i + 8⟩])
    (h : ArmInput L P s .ASSIGN c pl cp sp high)
    (space : AssignWriteOk P s c pl cp sp high i w)
    (bound : i < s.stack.length) (value : valWord pl s.accu = some w)
    (body : ∀ d, DispatchPost c .ASSIGN (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧
        StackPost d pl pc sp (tag64 0) (writeLog d.σ.mem (assignLog sp i w)) after) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := pc, accu := .unit, stack := s.stack.set i s.accu} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nb, after, hb, post⟩ := body d dp
  refine ⟨nb, after, hb, ?_⟩
  refine assign_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space bound value
    ?_ h.geometry h.native
  simpa only [dp.memory] using post.after_dispatch dp

end OCaml.Vm.Sim
