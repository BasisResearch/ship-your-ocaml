import OCaml.Vm.Sim.BlockAllocation
import OCaml.Vm.Sim.ReturnRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Partial closure created by the insufficient-arity GRAB path. -/
def grabClosure (s : St) : Obj :=
  .block closureTag ([.code (s.pc - 1), Val.ofInt 2, s.env] ++ s.stack.take (1 + s.extra))

def grabState (s : St) (dest : Nat) (savedEnv : Val) (savedExtra : BitVec 63) (rest : List Val) : St :=
  {s with pc := dest, accu := .ptr (s.heap.alloc (grabClosure s)).2 0,
          heap := (s.heap.alloc (grabClosure s)).1, env := savedEnv, extra := savedExtra.toNat, stack := rest}

/-- The partial closure captures only old reachable values. -/
theorem grab_allocation_roots {P : Prog} {s : St} : AllocationRoots P s (grabClosure s) := by
  apply block_allocation_roots
  intro v member l loc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl) | member)
  · simp [Val.loc?] at loc
  · simp [Val.ofInt, Val.loc?] at loc
  · exact Live.root (by simp [roots]) loc
  · exact Live.root (by simp [roots, List.mem_of_mem_take member]) loc

/-- Allocation separation and placement, supplied by the G1 nursery invariant.
The write log includes the young pointer, header and all initialized fields. -/
structure GrabWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high a : Nat) (log : List WEntry) : Prop where
  placed : pl.φ (s.heap.alloc (grabClosure s)).2 = some a
  separate : AllocationOutside P s pl a (grabClosure s)
  payload : PayloadOutside log P s c pl cp sp
  image : ImageOutside log
  bindings : BindingsOutside log P c
  /-- the log's nursery reservation for the new object (the allocation summary) -/
  reserve : NurseryReserve c log a (grabClosure s).wosize (grabClosure s).wosize

  /-- all the allocation's stores lie in the allocator arena -/
  arena : LogInW [arenaWindow] (log)

/-- Final generated observations of the allocation and caller-frame path. -/
structure GrabPost (before : Config) (s : St) (pl : Place) (sp dest : Nat)
    (savedEnv : Val) (savedExtra : BitVec 63) (rest : List Val) (log : List WEntry) (after : Config) : Prop
    extends VmRegisters (grabState s dest savedEnv savedExtra rest) pl (sp + 8 * (s.extra + 4)) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after
  /-- the native stack pointer is unchanged -/
  nativeSp : gpr after 2 = gpr before 2

/-- GRAB allocation extends the represented heap and restores the caller
using the same frame payload rule as RETURN. -/
theorem grab_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high a dest : Nat} {savedEnv : Val} {savedExtra : BitVec 63}
    {rest : List Val} {log : List WEntry}
    (runtime : AllocationRuntime L.runtimeOk before log)
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (stack : s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest)
    (space : GrabWriteOk P s before pl cp sp high a log)
    (layout : ObjAt after pl cp a (grabClosure s))
    (post : GrabPost before s pl sp dest savedEnv savedExtra rest log after)
    (geometry : OCaml.LoopGeometry L P s before pl cp high)
    (native : NativePlaced before) :
    Running L P (grabState s dest savedEnv savedExtra rest) after := by
  have framed := (payload_of_repr data).frame_log space.payload post.memory post.output
  have allocated := framed.allocate grab_allocation_roots space.placed layout space.separate
  have saved := return_frame_values allocated stack
  have bound : s.extra + 4 ≤ s.stack.length := by
    have lengths := congrArg List.length stack
    simp only [List.length_drop, List.length_cons] at lengths
    omega
  have dropped : s.stack.drop (s.extra + 4) = rest := by
    calc
      _ = (s.stack.drop (1 + s.extra)).drop 3 := by rw [List.drop_drop]; congr 1; omega
      _ = rest := by rw [stack]; rfl
  have restored := return_payload (pc := dest) (extra := savedExtra.toNat) allocated bound saved.root
  have payload : VmPayload P (grabState s dest savedEnv savedExtra rest) after pl cp
      (sp + 8 * (s.extra + 4)) high := by
    simpa only [grabState, dropped] using restored
  exact running_of_payload payload (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      runtime after post.memory platform.runtime⟩ post.toVmRegisters post.loop
    (geometry.alloc_log (s' := grabState s dest savedEnv savedExtra rest) space.placed space.reserve rfl rfl
      space.payload.domain space.bindings.contents post.memory)
    (native.frame_log space.arena space.payload.domain post.memory post.nativeSp)

end OCaml.Vm.Sim
