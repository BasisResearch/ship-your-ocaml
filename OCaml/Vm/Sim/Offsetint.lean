import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.OffsetArithmetic
import OCaml.Vm.Sim.OffsetintSegment
import OCaml.Vm.Sim.OffsetintPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- OFFSETINT adds the sign-extended 32-bit shifted operand, matching the
corrected semantics even when shifting overflows the signed 32-bit range. -/
theorem offsetint_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 32} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .OFFSETINT c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w) (accu : s.accu = .int n) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 2, accu := .int (untag (tag64 n + offsetintOperand w))} c' := by
  have hc : gpr c Layout.reg_accu = some (tag64 n) :=
    represented_register h.accu (by rw [accu]; rfl)
  apply immediate_arm stable h
  intro d dp
  have read : bytesT4 d.σ.mem (pl.codeBase + 4 * (s.pc + 1)) = w :=
    operand.read32 h.code dp.memory
  have bp : SegSt (0x80003244#64) [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩, ⟨Register.x21, tag64 n⟩]
      (fun σ => Vsa.Sim.Code.CamlOffsetintLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x21 (by decide)).trans hc, trivial⟩,
      dp.good.minstret, dp.tick, offsetint_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_offsetint (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (tag64 n) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, read] at run
  obtain ⟨nb, after, _, hb, post⟩ := run operand.geometry.lower operand.geometry.upper
    operand.geometry.htif d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) :=
      PinsHold.get post.pins ⟨2, by simp⟩
    simpa only [show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2] using hp
  · have hp : gpr after Layout.reg_accu = some (tag64 n + offsetintOperand w) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [tag_offsetint] using hp

/-- The real OFFSETINT bytecode transition is simulated by the represented arm. -/
theorem offsetint_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 32} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .OFFSETINT c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w) (accu : s.accu = .int n)
    (step : stepI P s ⟨.OFFSETINT, [w.toInt]⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  have state : {s with pc := s.pc + 2, accu := .int (untag (tag64 n + offsetintOperand w))} = s' := by
    simpa [stepI, accu, St.adv, offsetintOperand_eq] using step
  rw [← state]
  exact offsetint_arm stable h operand accu

end OCaml.Vm.Sim
