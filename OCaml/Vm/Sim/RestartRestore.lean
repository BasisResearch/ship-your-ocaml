import OCaml.Vm.Sim.BlockRead
import OCaml.Vm.Sim.ValueLog
import OCaml.Vm.Sim.RootFrame
import OCaml.Vm.Sim.ReadOnly

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- RESTART recovers the environment and saved arguments from a partial closure. -/
def restartState (s : St) (fields : List Val) (env : Val) : St :=
  {s with pc := s.pc + 1, env := env, extra := s.extra + (fields.length - 3),
          stack := fields.drop 3 ++ s.stack}

def restartStart (sp : Nat) (fields : List Val) : Nat := sp - 8 * (fields.length - 3)

def restartLog (c : Config) (sp a : Nat) (fields : List Val) : List WEntry :=
  valueLog (restartStart sp fields) (stackWords c (a + 24) (fields.length - 3))

/-- Memory-side separation needed to install a partial closure's saved arguments. -/
structure RestartWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp high a : Nat) (fields : List Val) : Prop where
  room : 8 * (fields.length - 3) ≤ sp
  payload : StackEditOutside (restartLog c sp a fields) P s c pl cp high
  image : ImageOutside (restartLog c sp a fields)
  bindings : BindingsOutside (restartLog c sp a fields) P c

/-- Final native observations; source field representation is proved separately. -/
structure RestartPost (before : Config) (s : St) (pl : Place) (sp a : Nat)
    (fields : List Val) (env : Val) (after : Config) : Prop
    extends VmRegisters (restartState s fields env) pl (restartStart sp fields) after where
  good : GoodState after.σ
  memory : after.σ.mem = writeLog before.σ.mem (restartLog before sp a fields)
  output : after.σ.sailOutput = before.σ.sailOutput
  loop : LoopRegisters after

/-- Copying the saved closure fields restores RESTART's stack and root graph. -/
theorem restart_restore {L : OCaml.Layout} {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp high l a tag : Nat} {fields : List Val} {env : Val}
    (stable : WindowStable L.runtimeOk [⟨restartStart sp fields, sp⟩])
    (data : VmReprAt P s before pl cp sp high) (platform : PlatformOk L.runtimeOk before)
    (block : BlockSelection s.heap pl s.env l a tag fields) (environment : fields[2]? = some env)
    (space : RestartWriteOk P s before pl cp sp high a fields)
    (post : RestartPost before s pl sp a fields env after) :
    Running L P (restartState s fields env) after := by
  have arguments : ValueWords pl (fields.drop 3) (stackWords before (a + 24) (fields.length - 3)) :=
    block.words (payload_of_repr data) (by simp [roots]) 3
  have join : restartStart sp fields + 8 * (fields.length - 3) = sp := by
    unfold restartStart
    have room := space.room
    omega
  have payload := payload_copy_prefix (payload_of_repr data) (count := 0) (by omega)
    space.payload post.memory post.output (by simpa only [List.length_drop, Nat.mul_zero, Nat.add_zero] using join)
    arguments (fun _ selected => block.field_root (by simp [roots]) selected)
  have restored : VmPayload P {s with stack := fields.drop 3 ++ s.stack} after pl cp (restartStart sp fields) high := by
    simpa only [List.drop_zero] using payload
  have envRoot := (block.field environment).read_payload restored (by simp [roots])
  have entered := payload_env_of_root restored env envRoot.root
  have memoryFrame : FrameOn [⟨restartStart sp fields, sp⟩] before.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    have inside := value_log_in (restartStart sp fields) (stackWords before (a + 24) (fields.length - 3))
    simpa only [restartLog, stackWords, List.length_map, List.length_range, join] using inside
  exact running_of_payload (payload_pc (payload_extra entered (s.extra + (fields.length - 3))) (s.pc + 1))
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable before after memoryFrame platform.runtime⟩ post.toVmRegisters post.loop

end OCaml.Vm.Sim
