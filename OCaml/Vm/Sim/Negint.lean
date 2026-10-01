import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.ImmediateArithmetic
import OCaml.Vm.Sim.NegintSegment
import OCaml.Vm.Sim.NegintPins

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Represented NEGINT, using generated dispatch/body runs and the shared
immediate-result restoration rule. Dispatch readiness remains explicit. -/
theorem negint_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {n : BitVec 63}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .NEGINT c pl cp sp high) (accu : s.accu = .int n) :
    ∃ c', Plus c c' ∧ Running L P {s with pc := s.pc + 1, accu := .int (untag (2#64 - tag64 n))} c' := by
  rw [untag_neg]
  have hc : gpr c Layout.reg_accu = some (tag64 n) := by
    obtain ⟨w, hw, hv⟩ := h.accu
    rw [accu] at hv
    cases hv
    exact hw
  apply immediate_arm stable h
  intro d dp
  have bp : SegSt (0x80002d8c#64)
      [⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩,
       ⟨Register.x21, tag64 n⟩]
      (fun σ => Vsa.Sim.Code.CamlNegintLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨dp.nextCode, (dp.frame.frame Register.x21 (by decide)).trans hc, trivial⟩,
      dp.good.minstret, dp.tick, negint_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  obtain ⟨nb, after, hnb, hb, post⟩ := tr_negint _ _ d.σ.mem d.σ d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
          ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, codePc_succ] using hp
  · have hp : gpr after Layout.reg_accu = some
          ((0#64 + sign_extend (m := 64) (0x002#12)) - tag64 n) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [show sign_extend (m := 64) (0x002#12) = 2#64 from by decide,
      BitVec.zero_add, tag_neg] using hp

end OCaml.Vm.Sim
