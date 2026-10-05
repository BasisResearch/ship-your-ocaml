import OCaml.Vm.Sim.ClosureLayout
import OCaml.Vm.Sim.GrabNurseryInput
import OCaml.Vm.Sim.StackDrop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def closureCaptures (s : St) (count : Nat) : List Val :=
  if 0 < count then s.accu :: s.stack.take (count - 1) else []

def closureObject (s : St) (count dest : Nat) : Obj :=
  .block closureTag ([.code dest, Val.ofInt 2] ++ closureCaptures s count)

def closureState (s : St) (count dest : Nat) : St :=
  {s with pc := s.pc + 3, stack := s.stack.drop (count - 1),
          heap := (s.heap.alloc (closureObject s count dest)).1,
          accu := .ptr (s.heap.alloc (closureObject s count dest)).2 0}

def closureWords (c : Config) (sp count : Nat) (accu : BitVec 64) : List (BitVec 64) :=
  if 0 < count then accu :: stackWords c sp (count - 1) else []

def closurePushLog (sp count : Nat) (accu : BitVec 64) : List WEntry :=
  if 0 < count then [(sp - 8, 8, accu)] else []

def closureAllocationLog (c : Config) (pl : Place) (sp count dest a domain : Nat) (accu : BitVec 64) : List WEntry :=
  (closurePushLog sp count accu ++ grabReserveLog domain a) ++
    closureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (closureWords c sp count accu)

/-- A closure captures only roots already represented by the old accumulator/stack. -/
theorem closure_allocation_roots {P : Prog} {s : St} {count dest : Nat} :
    AllocationRoots P s (closureObject s count dest) := by
  apply block_allocation_roots
  intro v member l loc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl) | member)
  · simp [Val.loc?] at loc
  · simp [Val.ofInt, Val.loc?] at loc
  · by_cases positive : 0 < count
    · simp only [closureCaptures, positive, ite_true, List.mem_cons] at member
      rcases member with rfl | member
      · exact Live.root (by simp [roots]) loc
      · exact Live.root (by simp [roots, List.mem_of_mem_take member]) loc
    · simp only [closureCaptures, positive, ite_false, List.not_mem_nil] at member

theorem closure_words_length (c : Config) (sp count : Nat) (accu : BitVec 64) :
    (closureWords c sp count accu).length = count := by
  by_cases positive : 0 < count
  · simp only [closureWords, positive, ite_true, List.length_cons, stackWords, List.length_map, List.length_range]
    omega
  · simp only [closureWords, positive, ite_false, List.length_nil]
    omega

/-- Complete closure footprint and placement, supplied by the G1 invariant. -/
structure ClosureWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high count dest a domain : Nat) (accu : BitVec 64) : Prop where
  bound : count - 1 ≤ s.stack.length
  small : count + 2 < 2^32
  room : 8 ≤ a
  placed : pl.φ (s.heap.alloc (closureObject s count dest)).2 = some a
  separate : AllocationOutside P s pl a (closureObject s count dest)
  payload : PayloadOutside (closureAllocationLog c pl sp count dest a domain accu) P s c pl cp sp
  image : ImageOutside (closureAllocationLog c pl sp count dest a domain accu)
  bindings : BindingsOutside (closureAllocationLog c pl sp count dest a domain accu) P c
  /-- the nursery placement is apart from the VM stack window -/
  stackApart : OutWRange [stackWindow high] (a - 8) (8 * (closureObject s count dest).wosize + 8)
  /-- the allocation and all its stores lie in the allocator arena -/
  arenaEnd : a + 8 * (closureObject s count dest).wosize ≤ Vsa.Sim.DlHeap.heapEnd
  arena : LogInW [arenaWindow] (closureAllocationLog c pl sp count dest a domain accu)

structure ClosurePost (before : Config) (s : St) (pl : Place) (sp count dest a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop
    extends VmRegisters (closureState s count dest) pl (sp + 8 * (count - 1)) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (closureAllocationLog before pl sp count dest a domain accuWord)
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after
  /-- the native stack pointer is unchanged -/
  nativeSp : gpr after 2 = gpr before 2

/-- The native closure log extends the represented heap, consumes its captures,
and restores the loop-head platform invariant. -/
theorem closure_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high count dest a domain : Nat} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk before (closureAllocationLog before pl sp count dest a domain accu))
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (value : valWord pl s.accu = some accu)
    (space : ClosureWriteOk P s before pl cp sp high count dest a domain accu)
    (post : ClosurePost before s pl sp count dest a domain accu after)
    (geometry : StackGeometry P s before pl cp high)
    (native : NativePlaced before) :
    Running L P (closureState s count dest) after := by
  have captures : ValueWords pl (closureCaptures s count) (closureWords before sp count accu) := by
    by_cases positive : 0 < count
    · simp only [closureCaptures, closureWords, positive, ite_true]
      exact ValueWords.cons value (stack_value_words data.stack space.bound)
    · simp only [closureCaptures, closureWords, positive, ite_false]
      exact ValueWords.nil pl
  let reserved : Config := {before with σ := {before.σ with mem := writeLog before.σ.mem (closurePushLog sp count accu ++ grabReserveLog domain a)}}
  have objectMemory : after.σ.mem = writeLog reserved.σ.mem
      (closureLog a (BitVec.ofNat 64 (pl.codeBase + 4 * dest)) (closureWords before sp count accu)) := by
    rw [post.memory, closureAllocationLog, writeLog_append]
  have layout : ObjAt after pl cp a (closureObject s count dest) :=
    closure_log_layout space.room (by rw [closure_words_length]; exact space.small) captures objectMemory
  have framed := (payload_of_repr data).frame_log space.payload post.memory post.output
  have allocated := framed.allocate closure_allocation_roots space.placed layout space.separate
  have payload := payload_pc (payload_stack_drop allocated space.bound) (s.pc + 3)
  exact running_of_payload payload (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory, runtime after post.memory platform.runtime⟩
    post.toVmRegisters post.loop
    ((geometry.frame_log rfl rfl space.payload.domain space.bindings.contents post.memory).alloc space.placed space.stackApart space.arenaEnd rfl rfl)
    (native.frame_log space.arena space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
