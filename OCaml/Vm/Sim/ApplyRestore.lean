import OCaml.Vm.Sim.ApplyFramePayload
import OCaml.Vm.Sim.EnterFrame
import OCaml.Vm.Sim.WriteGeometry

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Abstract fixed-arity application: retain arguments above a saved caller frame. -/
def applyState (s : St) (arity dest : Nat) : St :=
  {s with pc := dest, env := s.accu, extra := arity - 1,
          stack := s.stack.take arity ++ [.code (s.pc + 1), s.env, Val.ofInt s.extra] ++ s.stack.drop arity}

/-- Geometry and separation for one fixed-arity application's concrete word log.
The loop invariant supplies these memory facts, independently of execution. -/
structure ApplyWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high : Nat) (args : List (BitVec 64)) (env : BitVec 64) : Prop where
  room : 24 ≤ sp
  reads : ∀ i, i < args.length → RamReadAt (sp + 8 * i) 8
  writes : ∀ entry ∈ applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
    env (tag64 (BitVec.ofNat 63 s.extra)), RamWriteAt entry.1 entry.2.1
  payload : StackEditOutside (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
    env (tag64 (BitVec.ofNat 63 s.extra))) P s c pl cp high
  enter : EnterOutside (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
    env (tag64 (BitVec.ofNat 63 s.extra))) c
  image : ImageOutside (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
    env (tag64 (BitVec.ofNat 63 s.extra)))
  bindings : BindingsOutside (applyFrameLog sp args (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
    env (tag64 (BitVec.ofNat 63 s.extra))) P c

/-- Named final observations supplied by each generated fixed-arity body. -/
structure ApplyPost (before : Config) (s : St) (pl : Place) (sp dest : Nat)
    (args : List (BitVec 64)) (savedEnv : BitVec 64) (after : Config) : Prop
    extends VmRegisters (applyState s args.length dest) pl (sp - 24) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (applyFrameLog sp args
    (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1))) savedEnv (tag64 (BitVec.ofNat 63 s.extra)))
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after

/-- Fixed-arity applications share one data/platform restoration proof. -/
theorem apply_frame_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {args : List (BitVec 64)} {env : BitVec 64}
    (stable : WindowStable L.runtimeOk [⟨sp - 24, sp + 8 * args.length⟩])
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (positive : 1 ≤ args.length) (small : args.length ≤ 3) (bound : args.length ≤ s.stack.length)
    (arguments : ValueWords pl (s.stack.take args.length) args) (envWord : valWord pl s.env = some env)
    (space : ApplyWriteOk P s before pl cp sp high args env)
    (post : ApplyPost before s pl sp dest args env after) : Running L P (applyState s args.length dest) after := by
  have payload := apply_frame_payload (payload_of_repr data) space.room positive small bound arguments envWord
    space.payload post.memory post.output
  have entered := payload_env_of_root payload s.accu (fun _ loc => Live.root (by simp [roots]) loc)
  have memoryFrame : FrameOn [⟨sp - 24, sp + 8 * args.length⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    have inside := apply_entries_in (sp - 24) (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)))
      env (tag64 (BitVec.ofNat 63 s.extra)) positive small
    have join : sp - 24 + 8 * (args.length + 3) = sp + 8 * args.length := by have room := space.room; omega
    simpa only [applyFrameLog, join] using inside
  exact running_of_payload (payload_pc (payload_extra entered (args.length - 1)) dest)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩ post.toVmRegisters post.loop

end OCaml.Vm.Sim
