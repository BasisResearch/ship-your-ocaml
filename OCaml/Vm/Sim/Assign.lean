import OCaml.Vm.Sim.AssignStore
import OCaml.Vm.Sim.IndexWord
import OCaml.Vm.Sim.AssignSegment
import OCaml.Vm.Sim.AssignPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- ASSIGN stores the accumulator into an existing stack slot and returns unit.
All effects follow from the generated store and shared stack-edit restoration. -/
theorem assign_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 64} {index : BitVec 32}
    (stable : WindowStable L.runtimeOk
      [⟨sp + 8 * index.toInt.toNat, sp + 8 * index.toInt.toNat + 8⟩])
    (h : ArmInput L P s .ASSIGN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) index)
    (nonnegative : 0 ≤ index.toInt)
    (space : AssignWriteOk P s c pl cp sp high index.toInt.toNat w)
    (bound : index.toInt.toNat < s.stack.length)
    (value : valWord pl s.accu = some w) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 2, accu := .unit, stack := s.stack.set index.toInt.toNat s.accu} c' := by
  have source := represented_register h.accu value
  have natAddress := stack_slot_nat h.toVmReprAt (List.getElem?_eq_getElem bound)
  apply assign_body_arm stable h space bound value
  intro d dp
  have read := operand.read32 h.code dp.memory
  have address : BitVec.ofNat 64 sp + BitVec.ofNat 64 (8 * index.toInt.toNat) =
      BitVec.ofNat 64 (sp + 8 * index.toInt.toNat) := (BitVec.ofNat_add _ _).symm
  have code : sp + 8 * index.toInt.toNat + 8 ≤ 0x800023dc ∨
      0x800023f8 ≤ sp + 8 * index.toInt.toNat :=
    image_word_code space.image (by decide) (by decide)
  obtain ⟨memoryAfter, memoryEq⟩ : ∃ mem : Std.ExtHashMap Nat (BitVec 8),
      mem = writeLog d.σ.mem (assignLog sp index.toInt.toNat w) := ⟨_, rfl⟩
  have bp : SegSt (0x800023dc#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x9, BitVec.ofNat 64 sp⟩, ⟨Register.x21, w⟩]
      (fun σ => Vsa.Sim.Code.CamlAssignLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
       (dp.frame.frame Register.x9 (by decide)).trans h.spReg,
       (dp.frame.frame Register.x21 (by decide)).trans source, trivial⟩,
      dp.good.minstret, dp.tick, assign_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_assign (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 sp) w d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    show sign_extend (m := 64) (0x000#12) = 0#64 from by decide, BitVec.add_zero,
    codePc_succ, operand.geometry.toNat, read, index_word index nonnegative, address] at run
  obtain ⟨nb, after, _, hb, post⟩ := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    space.window.lower space.window.upper space.window.htif space.window.aligned
    (by simpa only [natAddress] using code) memoryAfter
    (by rw [natAddress]; exact memoryEq) d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, ?_, hm.trans memoryEq, frame.out, ?_⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) :=
      PinsHold.get post.pins ⟨2, by simp⟩
    simpa only [show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2] using hp
  · exact PinsHold.get post.pins ⟨3, by simp⟩
  · exact PinsHold.get post.pins ⟨0, by simp⟩
  · intro r hr
    exact frame.frame r (by revert r; decide)

/-- A successful ASSIGN semantic step supplies the stack-index bound. -/
theorem assign_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 64} {index : BitVec 32}
    (stable : WindowStable L.runtimeOk
      [⟨sp + 8 * index.toInt.toNat, sp + 8 * index.toInt.toNat + 8⟩])
    (h : ArmInput L P s .ASSIGN c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) index)
    (nonnegative : 0 ≤ index.toInt)
    (space : AssignWriteOk P s c pl cp sp high index.toInt.toNat w)
    (value : valWord pl s.accu = some w)
    (step : stepI P s ⟨.ASSIGN, [index.toInt]⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  by_cases bound : index.toInt.toNat < s.stack.length
  · have state : {s with pc := s.pc + 2, accu := .unit, stack := s.stack.set index.toInt.toNat s.accu} = s' := by
      simpa [stepI, bound, St.adv] using Res.unguard step
    rw [← state]
    exact assign_arm stable h operand nonnegative space bound value
  · have step := Res.unguard step; simp [stepI, bound] at step

end OCaml.Vm.Sim
