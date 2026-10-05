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

/-- A same-size object replacement keeps the stack geometry. -/
theorem StackGeometry.heap_set {P : Prog} {s s' : St} {c c' : Config} {pl : Place}
    {cp : ChanPlace} {high l : Nat} {old new : Obj} {log : List WEntry}
    (g : StackGeometry P s c pl cp high) (selected : s.heap.get? l = some old)
    (size : new.wosize = old.wosize) (heap : s'.heap = s.heap.set l new)
    (world : s'.world = s.world) (domain : OutLRange log Layout.sym_Caml_state 8)
    (contents : OutLRange log (Layout.sym_caml_prim_table + Layout.off_prim_contents) 8)
    (memory : c'.σ.mem = writeLog c.σ.mem log) : StackGeometry P s' c' pl cp high := by
  have g' : StackGeometry P {s with world := s'.world} c' pl cp high :=
    g.frame_log rfl world domain contents memory
  refine g'.transport (s' := s') ?_ rfl rfl rfl
  intro q o' found
  rw [heap] at found
  by_cases equal : q = l
  · subst q
    rw [heap_set_here new selected] at found
    cases found
    exact ⟨old, selected, size.symm⟩
  · rw [heap_set_other _ _ _ _ (Ne.symm equal)] at found
    exact ⟨o', found, rfl⟩

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
    (post : StackPost c pl pc sp (tag64 0) (writeLog c.σ.mem (fieldLog a i w)) after)
    (geometry : StackGeometry P s c pl cp high)
    (native : NativePlaced c) :
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
    (geometry.heap_set selected (by simp only [Obj.wosize, List.length_set]) rfl rfl space.payload.domain space.bindings.contents post.memory)
    (native.frame_vm (ws := [⟨a + 8 * i, a + 8 * i + 8⟩]) (by simp only [fieldLog, LogInW, InsideW, or_false, and_true]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩) (by simp only [List.mem_singleton, forall_eq]; have := geometry.heapArena l a _ placed selected; simp only [Obj.wosize] at this; omega) space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
