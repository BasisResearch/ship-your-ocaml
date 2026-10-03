import OCaml.Vm.Sim.ValueLog
import OCaml.Vm.Sim.EnterFrame
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Tail application retains arguments while dropping the current local frame. -/
def tailcallState (s : St) (arity slots dest : Nat) : St :=
  {s with pc := dest, env := s.accu, extra := s.extra + arity - 1,
          stack := s.stack.take arity ++ s.stack.drop slots}

/-- Destination of a tail call's argument move in a downward-growing stack. -/
def tailcallStart (sp arity slots : Nat) : Nat := sp + 8 * (slots - arity)

/-- Geometry and separation of the argument move. The loop invariant supplies
these concrete memory obligations; no field assumes a machine result. -/
structure TailcallWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high slots : Nat) (args : List (BitVec 64)) : Prop where
  fits : args.length ≤ slots
  bound : slots ≤ s.stack.length
  reads : ∀ i, i < args.length → RamReadAt (sp + 8 * i) 8
  writes : ∀ entry ∈ valueLog (tailcallStart sp args.length slots) args,
    RamWriteAt entry.1 entry.2.1
  payload : StackEditOutside (valueLog (tailcallStart sp args.length slots) args) P s c pl cp high
  enter : EnterOutside (valueLog (tailcallStart sp args.length slots) args) c
  image : ImageOutside (valueLog (tailcallStart sp args.length slots) args)
  bindings : BindingsOutside (valueLog (tailcallStart sp args.length slots) args) P c

/-- Concrete observations exported by generated tail-call bodies. -/
structure TailcallPost (before : Config) (s : St) (pl : Place) (sp slots dest : Nat)
    (args : List (BitVec 64)) (after : Config) : Prop
    extends VmRegisters (tailcallState s args.length slots dest) pl
      (tailcallStart sp args.length slots) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (valueLog (tailcallStart sp args.length slots) args)
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after

/-- Every tail-call arity shares argument-copy and platform restoration. -/
theorem tailcall_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high slots dest : Nat} {args : List (BitVec 64)}
    (stable : WindowStable L.runtimeOk [⟨tailcallStart sp args.length slots, sp + 8 * slots⟩])
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (arguments : ValueWords pl (s.stack.take args.length) args)
    (space : TailcallWriteOk P s before pl cp sp high slots args)
    (post : TailcallPost before s pl sp slots dest args after) :
    Running L P (tailcallState s args.length slots dest) after := by
  have bound : args.length ≤ s.stack.length := Nat.le_trans space.fits space.bound
  have join : tailcallStart sp args.length slots + 8 * args.length = sp + 8 * slots := by
    unfold tailcallStart
    have fits := space.fits
    omega
  have payload := payload_copy_prefix (payload_of_repr data) space.bound space.payload post.memory post.output
    (by simpa only [List.length_take, Nat.min_eq_left bound] using join) arguments
    (fun v member l loc => Live.root (by simp [roots, List.mem_of_mem_take member]) loc)
  have entered := payload_env_of_root payload s.accu (fun _ loc => Live.root (by simp [roots]) loc)
  have memoryFrame : FrameOn [⟨tailcallStart sp args.length slots, sp + 8 * slots⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simpa only [join] using value_log_in (tailcallStart sp args.length slots) args
  exact running_of_payload (payload_pc (payload_extra entered (s.extra + args.length - 1)) dest)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩ post.toVmRegisters post.loop

end OCaml.Vm.Sim
