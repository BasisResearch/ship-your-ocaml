import OCaml.Vm.Sim.ClosurerecStackWords
import OCaml.Vm.Sim.ClosurerecReturn
import OCaml.Vm.Sim.Immediate

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

def closurerecState (s : St) (count dest : Nat) (targets : List Nat) : St :=
  {s with pc := s.pc + 3 + (targets.length + 1),
          heap := (s.heap.alloc (closurerecObject s count (dest :: targets))).1,
          accu := .ptr (s.heap.alloc (closurerecObject s count (dest :: targets))).2 0,
          stack := closurerecStack s count (targets.length + 1)
            (s.heap.alloc (closurerecObject s count (dest :: targets))).2}

/-- The G1 supplier reserves the complete object and surviving stack footprint.
Consumed old stack slots may be overwritten by the returned function pointers. -/
structure ClosurerecWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp count dest a domain : Nat) (accu : BitVec 64) (targets : List Nat) : Prop where
  bound : count - 1 ≤ s.stack.length
  small : closurerecSize (targets.length + 1) count < 2^32
  room : 8 ≤ a
  tailRoom : 8 ≤ sp + 8 * (count - 1)
  stackRoom : 8 * targets.length ≤ closurerecStackStart sp count
  heapBelow : closurerecCaptureBase a (targets.length + 1) + 8 * count ≤
    closurerecStackStart sp count - 8 * targets.length
  placed : pl.φ (s.heap.alloc (closurerecObject s count (dest :: targets))).2 = some a
  separate : AllocationOutside P s pl a (closurerecObject s count (dest :: targets))
  core : PayloadCoreOutside (closurerecFullLog c pl sp count dest a domain accu targets) P s c pl cp
  heap : ∀ l b o, Live s.heap (roots P s) l → pl.φ l = some b → s.heap.get? l = some o →
    ObjectOutside (closurerecFullLog c pl sp count dest a domain accu targets) b o
  tail : ∀ i v, (s.stack.drop (count - 1))[i]? = some v →
    OutLRange (closurerecFullLog c pl sp count dest a domain accu targets)
      (sp + 8 * (count - 1) + 8 * i) 8
  trap : OutLRange (closurerecFullLog c pl sp count dest a domain accu targets)
    ((word c Layout.sym_Caml_state).toNat + Layout.off_trapsp) 8
  bindings : BindingsOutside (closurerecFullLog c pl sp count dest a domain accu targets) P c

/-- Restore the full represented state after the proved native constructor. -/
theorem closurerec_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high count dest a domain : Nat} {accu : BitVec 64}
    {targets : List Nat}
    (runtime : AllocationRuntime L.runtimeOk before (closurerecFullLog before pl sp count dest a domain accu targets))
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (loop : LoopRegisters before) (value : valWord pl s.accu = some accu)
    (space : ClosurerecWriteOk P s before pl cp sp count dest a domain accu targets)
    (post : ClosurerecReturned before pl s.pc sp count dest a domain accu targets after)
    (geometry : StackGeometry P s before pl cp high)
    (nursery : NurseryPlacement P pl high a (closurerecObject s count (dest :: targets)))
    (domainApart : OutWRange [⟨(word before Layout.sym_Caml_state).toNat,
      (word before Layout.sym_Caml_state).toNat + Layout.domainStateBytes⟩] (a - 8)
      (8 * (closurerecObject s count (dest :: targets)).wosize + 8))
    (arena : LogInW [arenaWindow] (closurerecFullLog before pl sp count dest a domain accu targets))
    (native : NativePlaced before) :
    Running L P (closurerecState s count dest targets) after := by
  have captures : ValueWords pl (closureCaptures s count) (closureWords before sp count accu) := by
    by_cases positive : 0 < count
    · simp only [closureCaptures, closureWords, positive, ite_true]
      exact ValueWords.cons value (stack_value_words data.stack space.bound)
    · simp only [closureCaptures, closureWords, positive, ite_false]
      exact ValueWords.nil pl
  have layout := closurerec_log_layout (cp := cp) space.room space.stackRoom space.heapBelow space.small captures post.memory
  have tail := stack_frame_log (stack_drop data.stack space.bound) space.tail post.memory
  have tailAddress : sp + 8 * (count - 1) = closurerecStackStart sp count + 8 := by
    unfold closurerecStackStart
    have room := space.tailRoom
    omega
  rw [tailAddress] at tail
  have words := closurerec_stack_words space.placed space.stackRoom
    (by have hb := space.heapBelow; unfold closurerecCaptureBase at hb; omega) tail post.memory
  have domain : word after Layout.sym_Caml_state = word before Layout.sym_Caml_state :=
    Reloc.bytesT_congr (copied_of_writeLog post.memory space.core.domain)
  have trap : word after ((word before Layout.sym_Caml_state).toNat + Layout.off_trapsp) =
      word before ((word before Layout.sym_Caml_state).toNat + Layout.off_trapsp) :=
    Reloc.bytesT_congr (copied_of_writeLog post.memory space.trap)
  have payload := payload_allocate_stack (payload_of_repr data) space.core space.heap post.memory post.frame.out
    (by rw [domain, trap]; exact data.trapsp) closurerec_allocation_roots space.placed layout space.separate
    words closurerec_stack_roots
  apply running_of_payload (payload_pc payload (s.pc + 3 + (targets.length + 1)))
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, post.image, runtime after post.memory platform.runtime⟩
  case geometry =>
    exact (geometry.alloc (s' := closurerecState s count dest targets) space.placed nursery domainApart rfl rfl).frame_log rfl rfl
      space.core.domain space.bindings.contents post.memory
  case native =>
    exact native.frame_log arena space.core.domain post.memory (post.frame.frame (gprReg 2) (by decide))
  · refine ⟨post.pcAt, post.codeReg, post.stackReg, ⟨BitVec.ofNat 64 a, post.accu, ?_⟩, ?_, ?_⟩
    · simp only [closurerecState, valWord, space.placed, Option.map_some, Nat.mul_zero, Nat.add_zero]
    · obtain ⟨w, reg, represented⟩ := data.env
      exact ⟨w, (post.frame.frame Register.x25 (by decide)).trans reg, represented⟩
    · exact (post.frame.frame Register.x18 (by decide)).trans data.extra
  · exact loopRegisters_frame (fun r hr => post.frame.frame r (by revert r; decide)) loop

end OCaml.Vm.Sim
