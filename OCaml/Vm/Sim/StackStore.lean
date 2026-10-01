import OCaml.Vm.Sim.StackConsume
import OCaml.Vm.Sim.StackPush
import OCaml.Vm.Primitives.ImageFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- The one-word push log, shared by all PUSH-prefixed opcode families. -/
def pushLog (sp : Nat) (w : BitVec 64) : List WEntry := [(sp - 8, 8, w)]

/-- Static placement and separation obligations for a stack push. These are
memory facts, not execution assumptions; the eventual invariant adapter supplies them. -/
structure PushWriteOk (P : Prog) (s : St) (c : Config) (pl : Place) (cp : ChanPlace)
    (sp : Nat) (w : BitVec 64) : Prop where
  room : 8 ≤ sp
  address : sp - 8 < 2^64
  window : WriteWindow (BitVec.ofNat 64 (sp - 8)) 8
  payload : PayloadOutside (pushLog sp w) P s c pl cp sp
  image : ImageOutside (pushLog sp w)
  bindings : BindingsOutside (pushLog sp w) P c

theorem PushWriteOk.toNat {P s c pl cp sp w} (h : PushWriteOk P s c pl cp sp w) :
    (BitVec.ofNat 64 (sp - 8)).toNat = sp - 8 := Nat.mod_eq_of_lt h.address

/-- Global image separation supplies every generated arm's local fetch window. -/
theorem PushWriteOk.code {P s c pl cp sp w lo hi} (h : PushWriteOk P s c pl cp sp w)
    (lower : Image.textBase ≤ lo) (upper : hi ≤ Image.textBase + Image.textSize) :
    sp - 8 + 8 ≤ lo ∨ hi ≤ sp - 8 := by
  have outside := h.image.text
  change (Image.textBase + Image.textSize ≤ sp - 8 ∨
    sp - 8 + 8 ≤ Image.textBase) ∧ True at outside
  rcases outside.1 with left | right <;> omega

/-- Every old stack slot outside the push log has its original total word. -/
theorem PushWriteOk.stack_read {P s c pl cp sp w i v}
    {memoryAfter : Std.ExtHashMap Nat (BitVec 8)} (h : PushWriteOk P s c pl cp sp w)
    (selected : s.stack[i]? = some v)
    (memory : memoryAfter = writeLog c.σ.mem (pushLog sp w)) :
    LeanRV64DExecutable.Functions.sign_extend (m := 64)
      (bytesT8 memoryAfter (sp + 8 * i)) = word c (sp + 8 * i) := by
  have frame := bytesT_writeLog_out c.σ.mem (h.payload.stack i v selected)
  rw [memory]
  simpa only [word, bytesT_eight_eq, LeanRV64DExecutable.Functions.sign_extend,
    Sail.BitVec.signExtend, BitVec.signExtend_eq] using frame

/-- Ordinary bytecode operands retain their value after the separated stack write. -/
theorem PushWriteOk.operand_read32 {P s c pl cp sp pushed i operandWord}
    {memoryAfter : Std.ExtHashMap Nat (BitVec 8)}
    (space : PushWriteOk P s c pl cp sp pushed)
    (code : CodeRepr P.code pl.codeBase c)
    (operand : OperandAt P pl i operandWord)
    (memory : memoryAfter = writeLog c.σ.mem (pushLog sp pushed)) :
    bytesT4 memoryAfter (pl.codeBase + 4 * i) = operandWord := by
  have frame := bytesT_writeLog_out c.σ.mem (space.payload.code i operandWord operand.fetch)
  rw [bytesT_four_eq] at frame
  rw [memory, frame]
  simpa only [bytesT_four_eq] using operand.read32 (d := c) code rfl

abbrev PushPost (before : Config) (pl : Place) (pc sp : Nat) (pushed result : BitVec 64)
    (after : Config) : Prop :=
  StackPost before pl pc (sp - 8) result (writeLog before.σ.mem (pushLog sp pushed)) after

/-- Frame the represented payload through the store, add the saved accumulator,
then select the result. Runtime preservation is confined to the single stack word. -/
theorem push_value_restore {L : OCaml.Layout} {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {w result : BitVec 64} {v : Val}
    (stable : WindowStable L.runtimeOk [⟨sp - 8, sp⟩])
    (data : VmReprAt P s c pl cp sp high) (platform : PlatformOk L.runtimeOk c)
    (loop : LoopRegisters c) (space : PushWriteOk P s c pl cp sp w)
    (pushed : valWord pl s.accu = some w) (value : valWord pl v = some result)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (post : PushPost c pl pc sp w result after) :
    Running L P {s with pc := pc, accu := v, stack := s.accu :: s.stack} after := by
  have stored : word after (sp - 8) = w := by
    rw [word, post.memory]
    exact word_writeLog c.σ.mem (sp - 8) w
  have framed := (payload_of_repr data).frame_log space.payload post.memory post.output
  have payload := payload_stack_push framed space.room (by rw [stored]; exact pushed)
  have selected := payload.accu_of_root v (fun l hl => live_stack_push (root l hl))
  have memoryFrame : FrameOn [⟨sp - 8, sp⟩] c.σ.mem after.σ.mem := by
    rw [post.memory]
    apply frameOn_writeLog
    simp only [pushLog, LogInW, InsideW, or_false, and_true]
    have room := space.room
    exact ⟨Nat.le_refl _, by omega⟩
  apply running_of_payload (payload_pc selected pc)
    (bindings_frame_log data.primitives space.bindings post.memory)
    ⟨post.good, image_of_writeLog platform.image space.image post.memory,
      stable c after memoryFrame platform.runtime⟩ ?_ ?_
  · refine ⟨post.head, post.code, post.stack, ⟨result, post.accu, value⟩, ?_, ?_⟩
    · obtain ⟨e, he, hv⟩ := data.env
      exact ⟨e, (post.preserved _ (by decide)).trans he, hv⟩
    · exact (post.preserved _ (by decide)).trans data.extra
  · exact ⟨(post.preserved _ (by decide)).trans loop.dispatchTable,
      (post.preserved _ (by decide)).trans loop.opcodeBound,
      (post.preserved _ (by decide)).trans loop.pending,
      (post.preserved _ (by decide)).trans loop.domain⟩

/-- Shared dispatch composition for stack-writing bodies. -/
theorem push_value_arm {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high pc : Nat} {w result : BitVec 64} {v : Val}
    (stable : WindowStable L.runtimeOk [⟨sp - 8, sp⟩])
    (h : ArmInput L P s op c pl cp sp high) (space : PushWriteOk P s c pl cp sp w)
    (pushed : valWord pl s.accu = some w) (value : valWord pl v = some result)
    (root : ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (body : ∀ d, DispatchPost c op (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d →
      ∃ nb after, StepsN nb d after ∧ PushPost d pl pc sp w result after) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := pc, accu := v, stack := s.accu :: s.stack} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nb, after, hb, post⟩ := body d dp
  refine ⟨nb, after, hb, ?_⟩
  apply push_value_restore stable h.toVmReprAt h.running.platform h.dispatch.loop space pushed value root
  exact ⟨post.good, post.head, post.code, post.stack, post.accu,
    post.memory.trans (congrArg (fun m => writeLog m (pushLog sp w)) dp.memory),
    post.output.trans dp.frame.out,
    fun r hr => (post.preserved r hr).trans (dp.frame.frame r (by revert r; decide))⟩

end OCaml.Vm.Sim
