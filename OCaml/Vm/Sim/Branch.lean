import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.BranchArithmetic
import OCaml.Vm.Sim.BranchSegment
import OCaml.Vm.Sim.BranchPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- BRANCH restores the same VM data at its signed relative bytecode target.
The operand contract supplies the read; target success comes from stepI. -/
theorem branch_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high dest : Nat} {w : BitVec 32}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .BRANCH c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) w)
    (jump : target s.pc 0 w.toInt = some dest) :
    ∃ c', Plus c c' ∧ Running L P {s with pc := dest} c' := by
  apply control_arm stable h
  intro d dp accu haccu _value
  have read : bytesT4 d.σ.mem (pl.codeBase + 4 * (s.pc + 1)) = w :=
    operand.read32 h.code dp.memory
  have bp : SegSt (0x80003104#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩]
      (fun σ => Vsa.Sim.Code.CamlBranchLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc, dp.nextCode, trivial⟩,
      dp.good.minstret, dp.tick, branch_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_branch (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc))
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat, read] at run
  obtain ⟨nb, after, _, hb, post⟩ := run operand.geometry.lower operand.geometry.upper
    operand.geometry.htif d (by simpa only [codePc_succ] using bp)
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
        (BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) +
          (BitVec.ofInt 64 w.toInt <<< (2 : Nat))) := PinsHold.get post.pins ⟨0, by simp⟩
    have address : BitVec.ofNat 64 (pl.codeBase + 4 * (s.pc + 1)) +
        (BitVec.ofInt 64 w.toInt <<< (2 : Nat)) = BitVec.ofNat 64 (pl.codeBase + 4 * dest) := by
      simpa only [Nat.add_zero] using relative_code_word pl jump
    simpa only [address] using hp
  · exact (frame.frame Register.x21 (by decide)).trans haccu

end OCaml.Vm.Sim
