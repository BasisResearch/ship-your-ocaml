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
  young : YoungOutside (valueLog (tailcallStart sp args.length slots) args) c
  bindings : BindingsOutside (valueLog (tailcallStart sp args.length slots) args) P c

/-- Memory-side facts independent of the concrete argument-copy order. -/
structure TailcallMemoryOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high arity slots : Nat) (log : List WEntry) : Prop where
  fits : arity ≤ slots
  bound : slots ≤ s.stack.length
  payload : StackEditOutside log P s c pl cp high
  image : ImageOutside log
  young : YoungOutside log c
  bindings : BindingsOutside log P c
  inside : LogInW [⟨tailcallStart sp arity slots, sp + 8 * slots⟩] log

/-- Concrete final observations, with the actual forward or backward write log. -/
structure TailcallPostWith (log : List WEntry) (before : Config) (s : St) (pl : Place)
    (sp slots dest arity : Nat) (after : Config) : Prop
    extends VmRegisters (tailcallState s arity slots dest) pl
      (tailcallStart sp arity slots) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem log
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after
  /-- the native stack pointer is unchanged -/
  nativeSp : gpr after 2 = gpr before 2

/-- Fixed-arity forward copies specialize the order-independent observations. -/
abbrev TailcallPost (before : Config) (s : St) (pl : Place) (sp slots dest : Nat)
    (args : List (BitVec 64)) (after : Config) : Prop :=
  TailcallPostWith (valueLog (tailcallStart sp args.length slots) args)
    before s pl sp slots dest args.length after

/-- Restore a tail call from checked argument readbacks in any native store order. -/
theorem tailcall_restore_of_log {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high slots dest arity : Nat} {log : List WEntry}
    (stable : WindowStable L.runtimeOk [⟨tailcallStart sp arity slots, sp + 8 * slots⟩])
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (space : TailcallMemoryOk P s before pl cp sp high arity slots log)
    (values : ∀ i v, (s.stack.take arity)[i]? = some v →
      valWord pl v = some (word after (tailcallStart sp arity slots + 8 * i)))
    (post : TailcallPostWith log before s pl sp slots dest arity after)
    (geometry : OCaml.LoopGeometry L P s before pl cp high)
    (native : NativePlaced before) :
    Running L P (tailcallState s arity slots dest) after := by
  have bound : arity ≤ s.stack.length := Nat.le_trans space.fits space.bound
  have join : tailcallStart sp arity slots + 8 * arity = sp + 8 * slots := by
    unfold tailcallStart
    have fits := space.fits
    omega
  have payload := payload_replace_prefix (payload_of_repr data) space.bound space.payload space.inside
    post.memory post.output (by simpa only [List.length_take, Nat.min_eq_left bound] using join) values
    (fun v member l loc => Live.root (by simp [roots, List.mem_of_mem_take member]) loc)
  have entered := payload_env_of_root payload s.accu (fun _ loc => Live.root (by simp [roots]) loc)
  have memoryFrame : FrameOn [⟨tailcallStart sp arity slots, sp + 8 * slots⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    exact frameOn_writeLog _ _ _ space.inside
  exact running_of_payload (payload_pc (payload_extra entered (s.extra + arity - 1)) dest)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩ post.toVmRegisters post.loop
    (geometry.frame_log rfl rfl space.payload.core.domain space.bindings.contents space.young post.memory)
    (native.frameOn memoryFrame (by simp only [List.mem_singleton, forall_eq]; exact geometry.stack_below (by have := data.stack.1; have := space.bound; omega)) (Reloc.bytesT_congr (copied_of_writeLog post.memory space.payload.core.domain)) post.nativeSp)

/-- Every fixed-arity tail call specializes the shared argument-copy restoration. -/
theorem tailcall_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high slots dest : Nat} {args : List (BitVec 64)}
    (stable : WindowStable L.runtimeOk [⟨tailcallStart sp args.length slots, sp + 8 * slots⟩])
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (arguments : ValueWords pl (s.stack.take args.length) args)
    (space : TailcallWriteOk P s before pl cp sp high slots args)
    (post : TailcallPost before s pl sp slots dest args after)
    (geometry : OCaml.LoopGeometry L P s before pl cp high) (native : NativePlaced before) :
    Running L P (tailcallState s args.length slots dest) after := by
  have join : tailcallStart sp args.length slots + 8 * args.length = sp + 8 * slots := by
    unfold tailcallStart
    have fits := space.fits
    omega
  have memory : TailcallMemoryOk P s before pl cp sp high args.length slots
      (valueLog (tailcallStart sp args.length slots) args) :=
    ⟨space.fits, space.bound, space.payload, space.image, space.young, space.bindings,
      by simpa only [join] using value_log_in (tailcallStart sp args.length slots) args⟩
  exact tailcall_restore_of_log stable data platform memory (value_log_words arguments post.memory) post
    geometry native

end OCaml.Vm.Sim
