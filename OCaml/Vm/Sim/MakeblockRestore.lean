import OCaml.Vm.Sim.BlockAllocation
import OCaml.Vm.Sim.GrabNurseryInput
import OCaml.Vm.Sim.StackDrop

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def makeblockObject (s : St) (count tag : Nat) : Obj :=
  .block tag (s.accu :: s.stack.take (count - 1))

def makeblockState (s : St) (width count tag : Nat) : St :=
  {s with pc := s.pc + width, stack := s.stack.drop (count - 1),
          heap := (s.heap.alloc (makeblockObject s count tag)).1,
          accu := .ptr (s.heap.alloc (makeblockObject s count tag)).2 0}

def makeblockWords (c : Config) (sp count : Nat) (accu : BitVec 64) : List (BitVec 64) :=
  accu :: stackWords c sp (count - 1)

def makeblockLog (c : Config) (sp count tag a domain : Nat) (accu : BitVec 64) : List WEntry :=
  grabReserveLog domain a ++ blockLog a tag (makeblockWords c sp count accu)

/-- MAKEBLOCK captures its represented accumulator and the consumed stack prefix. -/
theorem makeblock_allocation_roots {P : Prog} {s : St} {count tag : Nat} :
    AllocationRoots P s (makeblockObject s count tag) := by
  apply block_allocation_roots
  intro v member l loc
  rcases List.mem_cons.mp member with rfl | member
  · exact Live.root (by simp [roots]) loc
  · exact Live.root (by simp [roots, List.mem_of_mem_take member]) loc

/-- Concrete allocation footprint and fresh placement for all block arities. -/
structure MakeblockWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high count tag a domain : Nat) (accu : BitVec 64) : Prop where
  positive : 0 < count
  bound : count - 1 ≤ s.stack.length
  small : count < 2^32
  tagBound : tag < 256
  room : 8 ≤ a
  placed : pl.φ (s.heap.alloc (makeblockObject s count tag)).2 = some a
  separate : AllocationOutside P s pl a (makeblockObject s count tag)
  payload : PayloadOutside (makeblockLog c sp count tag a domain accu) P s c pl cp sp
  image : ImageOutside (makeblockLog c sp count tag a domain accu)
  bindings : BindingsOutside (makeblockLog c sp count tag a domain accu) P c
  /-- the log's nursery reservation for the new object (the allocation summary) -/
  reserve : ∃ words, NurseryReserve c (makeblockLog c sp count tag a domain accu) a (makeblockObject s count tag).wosize words

  /-- all the allocation's stores lie in the allocator arena -/
  arena : LogInW [arenaWindow] (makeblockLog c sp count tag a domain accu)

structure MakeblockPost (before : Config) (s : St) (pl : Place) (sp width count tag a domain : Nat)
    (accuWord : BitVec 64) (after : Config) : Prop
    extends VmRegisters (makeblockState s width count tag) pl (sp + 8 * (count - 1)) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (makeblockLog before sp count tag a domain accuWord)
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after
  /-- the native stack pointer is unchanged -/
  nativeSp : gpr after 2 = gpr before 2

/-- Shared represented restoration for fixed and variable block constructors.
Field layout follows from the exact initialized word log. -/
theorem makeblock_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high width count tag a domain : Nat} {accu : BitVec 64}
    (runtime : AllocationRuntime L.runtimeOk before (makeblockLog before sp count tag a domain accu))
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (value : valWord pl s.accu = some accu)
    (space : MakeblockWriteOk P s before pl cp sp high count tag a domain accu)
    (post : MakeblockPost before s pl sp width count tag a domain accu after)
    (geometry : ArmGeometry P s before pl cp high)
    (native : NativePlaced before) :
    Running L P (makeblockState s width count tag) after := by
  have fields := ValueWords.cons value (stack_value_words data.stack space.bound)
  have length : (makeblockWords before sp count accu).length = count := by
    simp only [makeblockWords, List.length_cons, stackWords, List.length_map, List.length_range]
    have positive := space.positive
    omega
  let reserved : Config := {before with σ := {before.σ with mem := writeLog before.σ.mem (grabReserveLog domain a)}}
  have objectMemory : after.σ.mem = writeLog reserved.σ.mem (blockLog a tag (makeblockWords before sp count accu)) := by
    rw [post.memory, makeblockLog, writeLog_append]
  have layout : ObjAt after pl cp a (makeblockObject s count tag) :=
    block_log_layout fields space.room (by change (makeblockWords before sp count accu).length < 2^32; rw [length]; exact space.small) space.tagBound objectMemory
  have framed := (payload_of_repr data).frame_log space.payload post.memory post.output
  have allocated := framed.allocate makeblock_allocation_roots space.placed layout space.separate
  have payload := payload_pc (payload_stack_drop allocated space.bound) (s.pc + width)
  exact running_of_payload payload (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory, runtime after post.memory platform.runtime⟩
    post.toVmRegisters post.loop
    (geometry.alloc_log (s' := makeblockState s width count tag) space.placed space.reserve.choose_spec rfl rfl
      space.payload.domain space.bindings.contents post.memory)
    (native.frame_log space.arena space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
