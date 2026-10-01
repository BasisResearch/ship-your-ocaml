import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.ImmediateArithmetic
import OCaml.Vm.Sim.ConstintSegment
import OCaml.Vm.Sim.ConstintPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- CONSTINT reads the ordinary signed bytecode operand and restores its
exact semantic integer. Code placement and cache exclusion remain explicit. -/
theorem constint_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .CONSTINT c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 2, accu := .int (BitVec.ofInt 63 w.toInt)} c' := by
  apply immediate_arm stable h
  intro d dp
  have read : bytesT4 d.σ.mem (pl.codeBase + 4 * (s.pc + 1)) = w :=
    operand.read32 h.code dp.memory
  have bp : SegSt (0x80001f88#64) [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩]
      (fun σ => Vsa.Sim.Code.CamlConstintLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc, trivial⟩,
      dp.good.minstret, dp.tick, constint_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_constint (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, read] at run
  obtain ⟨nb, after, _, hb, post⟩ := run operand.geometry.lower operand.geometry.upper
    operand.geometry.htif d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 8#64 =
      BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 2)) from codePc_add pl s.pc 2] using hp
  · have hp : gpr after Layout.reg_accu = some ((w.signExtend 64 <<< (1 : Nat)) + 1#64) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [tag_word32] using hp

end OCaml.Vm.Sim
