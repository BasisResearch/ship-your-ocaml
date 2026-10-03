import OCaml.Vm.Sim.HeapPayload
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Field-store geometry and non-heap separation supplied by the loop invariant. -/
structure FieldWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp a i : Nat) (w : BitVec 64) : Prop where
  address : a + 8 * i < 2^64
  window : WriteWindow (BitVec.ofNat 64 (a + 8 * i)) 8
  payload : HeapWriteOutside (fieldLog a i w) P s c pl cp sp
  image : ImageOutside (fieldLog a i w)
  bindings : BindingsOutside (fieldLog a i w) P c

/-- Restore a represented field replacement, unit result and complete platform. -/
theorem field_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a i tag pc : Nat}
    {fields : List Val} {value : Val} {w : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨a + 8 * i, a + 8 * i + 8⟩])
    (data : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (space : FieldWriteOk P s c pl cp sp a i w)
    (live : Live s.heap (roots P s) l) (placed : pl.φ l = some a)
    (selected : s.heap.get? l = some (.block tag fields))
    (room : 8 ≤ a) (bound : i < fields.length) (represented : valWord pl value = some w)
    (root : ∀ loc, value.loc? = some loc → Live s.heap (roots P s) loc)
    (post : StackPost c pl pc sp (tag64 0) (writeLog c.σ.mem (fieldLog a i w)) after) :
    Running L P {s with pc := pc, accu := .unit, heap := s.heap.set l (.block tag (fields.set i value))} after := by
  have payload := payload_field_written (payload_of_repr data) live placed selected room bound
    represented root space.payload post.memory post.output
  have memoryFrame : FrameOn [⟨a + 8 * i, a + 8 * i + 8⟩] c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [fieldLog, LogInW, InsideW, or_false, and_true]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  exact running_of_payload (payload_pc (payload.accu_int 0) pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable c after memoryFrame platform.runtime⟩
    (post.registers data rfl rfl rfl) (post.loopRegisters loop)

end OCaml.Vm.Sim
