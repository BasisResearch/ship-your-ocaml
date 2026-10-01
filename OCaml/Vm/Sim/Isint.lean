import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.IsintArithmetic
import OCaml.Vm.Sim.IsintSegment
import OCaml.Vm.Sim.IsintPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Represented ISINT for aligned placements and non-raw values. Alignment
is an explicit data-representation obligation, not a machine-body premise. -/
theorem isint_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .ISINT c pl cp sp high) (aligned : EvenPlace pl)
    (notRaw : ∀ x, s.accu ≠ .raw x) :
    ∃ c', Plus c c' ∧ Running L P {s with pc := s.pc + 1, accu := Val.ofBool s.accu.isInt} c' := by
  rw [ofBool_int]
  obtain ⟨w, hw, hv⟩ := h.accu
  apply immediate_arm stable h
  intro d dp
  have bp : SegSt (0x80003210#64)
      [⟨Register.x21, w⟩, ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩]
      (fun σ => Vsa.Sim.Code.CamlIsintLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x21 (by decide)).trans hw, dp.nextCode, trivial⟩,
      dp.good.minstret, dp.tick, isint_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  obtain ⟨nb, after, _, hb, post⟩ := tr_isint _ _ d.σ.mem d.σ d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
        ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, codePc_succ] using hp
  · have hp : gpr after Layout.reg_accu = some (isintWord w) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    rw [isintWord_repr aligned hv notRaw] at hp
    exact hp

end OCaml.Vm.Sim
