import OCaml.Vm.Sim.SwitchArithmetic
import OCaml.Vm.Sim.SwitchIntSegment
import OCaml.Vm.Sim.SwitchIntPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- The integer SWITCH path selects a represented table word and follows its
signed displacement from the table start. Operand geometry remains explicit. -/
theorem switch_int_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {n : BitVec 63} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .SWITCH c pl cp sp high)
    (accu : s.accu = .int n) (positive : 0 ≤ n.toInt)
    (operand : OperandAt P pl (s.pc + 2 + n.toNat) w)
    (jump : target s.pc 1 w.toInt = some dest) :
    ∃ after, Plus c after ∧ Running L P {s with pc := dest} after := by
  apply control_arm stable h
  intro d dp a haccu _
  have source := represented_register h.accu (by rw [accu]; rfl : valWord pl s.accu = some (tag64 n))
  have bp : SegSt (0x8000314c#64)
      [⟨Register.x21, tag64 n⟩, ⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩]
      (fun σ => Vsa.Sim.Code.CamlSwitchIntLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x21 (by decide)).trans source,
       (dp.frame.frame Register.x8 (by decide)).trans h.pc, trivial⟩,
      dp.good.minstret, dp.tick, switch_int_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have read := operand.read32 h.code dp.memory
  have run := tr_switch_int (tag64 n) (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x001#12) = 1#64 from by decide,
    show sign_extend (m := 64) (0x008#12) = 8#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
    BitVec.add_zero, tag_low_bit, switch_int_scale n positive, switch_table_word,
    operand.geometry.toNat, read] at run
  obtain ⟨nb, after, _, steps, post⟩ := run (by decide) operand.geometry.lower
    operand.geometry.upper operand.geometry.htif d bp
  obtain ⟨_, memory, frame⟩ := post.extra
  refine ⟨nb, after, steps, post.good, post.pcAt, ?_,
    (frame.frame Register.x21 (by decide)).trans haccu, memory, frame.out,
    immediate_preserved frame (by decide)⟩
  have pc : gpr after Layout.reg_pc = some
      ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) +
        (BitVec.ofInt 64 w.toInt <<< (2 : Nat))) := PinsHold.get post.pins ⟨0, by simp⟩
  have address : (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) +
      (BitVec.ofInt 64 w.toInt <<< (2 : Nat)) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
    rw [show (8#64) = BitVec.ofNat 64 (4 * 2) from rfl, codePc_add]
    simpa only [Nat.add_assoc] using relative_code_word pl jump
  simpa only [address] using pc

/-- A successful integer SWITCH supplies nonnegativity, bounds and the target.
The decoded table entry is matched to its represented code word explicitly. -/
theorem switch_int_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {n : BitVec 63} {w : BitVec 32}
    {sizes : Int} {table : List Int}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .SWITCH c pl cp sp high)
    (accu : s.accu = .int n)
    (operand : OperandAt P pl (s.pc + 2 + n.toNat) w)
    (entry : table[n.toNat]? = some w.toInt)
    (step : stepI P s ⟨.SWITCH, sizes :: table⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have bounds : 0 ≤ n.toInt ∧ n.toInt < (sizes.toNat % 65536 : Nat) := by
    by_cases good : 0 ≤ n.toInt ∧ n.toInt < (sizes.toNat % 65536 : Nat)
    · exact good
    · simp only [stepI, accu, good, ite_false, opt] at step
      cases step
  have taken : opt (target s.pc 1 w.toInt) (fun t => .next {s with pc := t}) = .next s' := by
    simpa only [stepI, accu, bounds, and_self, ite_true, entry, opt] using step
  cases jump : target s.pc 1 w.toInt with
  | none => simp [jump, opt] at taken
  | some dest =>
    have state : {s with pc := dest} = s' := by simpa [jump, opt] using taken
    rw [← state]
    exact switch_int_arm stable h accu bounds.1 operand jump

end OCaml.Vm.Sim
