import OCaml.Vm.Sim.GrabArithmetic
import OCaml.Vm.Sim.RootFrame
import OCaml.Vm.Sim.Immediate
import Vsa.Sim.FrameWriteSet
import OCaml.Vm.Sim.GrabFastSegment
import OCaml.Vm.Sim.GrabFastPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- When the supplied arguments satisfy GRAB, its generated read-only path
advances past the operand and deducts the requested extra arguments. -/
theorem grab_fast_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {count : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .GRAB c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (small : s.extra < 2^63) (enough : count.toInt.toNat ≤ s.extra) :
    ∃ after, Plus c after ∧ Running L P {s with pc := s.pc + 2, extra := s.extra - count.toInt.toNat} after := by
  apply dispatch_compose h.dispatch
  intro d dp
  have bp : SegSt (0x800027f4#64)
      [⟨Register.x8, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)⟩,
       ⟨Register.x18, BitVec.ofNat 64 s.extra⟩]
      (fun σ => Vsa.Sim.Code.CamlGrabFastLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨(dp.frame.frame Register.x8 (by decide)).trans h.pc,
      (dp.frame.frame Register.x18 (by decide)).trans h.extra, trivial⟩,
      dp.good.minstret, dp.tick, grab_fast_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_grab_fast (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc)) (BitVec.ofNat 64 s.extra) d.σ.mem d.σ
  simp only [show sign_extend (m := 64) (0x004#12) = 4#64 from by decide,
    codePc_succ, operand.geometry.toNat] at run
  obtain ⟨nb, after, _, steps, post⟩ := run operand.geometry.lower operand.geometry.upper operand.geometry.htif
    (sign_extend (m := 64) count) (by rw [operand.read32 h.code dp.memory])
    (grab_fast_guard s.extra count small nonnegative enough) d bp
  obtain ⟨_, memory, rawFrame⟩ := post.extra
  have frame := rawFrame.widenChecked
    (allowed := [Register.x15, Register.x12, Register.x18, Register.x8] ++ noiseRegs) (by decide)
  have preserved (r : Register) (avoid : ∀ q ∈ [Register.x15, Register.x12, Register.x18, Register.x8] ++ noiseRegs,
      (q == r) = false) (dispatch : ∀ q ∈ [Register.x15, Register.x23] ++ noiseRegs, (q == r) = false) :
      after.σ.regs.get? r = c.σ.regs.get? r := by
    exact (frame.frame r avoid).trans
      (dp.frame.frame r dispatch)
  have regs : VmRegisters {s with pc := s.pc + 2, extra := s.extra - count.toInt.toNat} pl sp after := by
    refine ⟨post.pcAt, ?_, ?_, ?_, ?_, ?_⟩
    · have pc : gpr after Layout.reg_pc = some
          (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + sign_extend (m := 64) (0x008#12) + sign_extend (m := 64) (0x000#12)) :=
        PinsHold.get post.pins ⟨0, by simp⟩
      simpa only [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 (4 * 2) from by decide,
        show sign_extend (m := 64) (0x000#12) = 0#64 from by decide, BitVec.add_zero, codePc_add] using pc
    · exact (preserved _ (by decide) (by decide)).trans h.spReg
    · obtain ⟨w, hw, hv⟩ := h.accu
      exact ⟨w, (preserved _ (by decide) (by decide)).trans hw, hv⟩
    · obtain ⟨w, hw, hv⟩ := h.env
      exact ⟨w, (preserved _ (by decide) (by decide)).trans hw, hv⟩
    · have extra : gpr after Layout.reg_extra = some (BitVec.ofNat 64 s.extra - sign_extend (m := 64) count) :=
        PinsHold.get post.pins ⟨1, by simp⟩
      simpa only [grab_fast_extra s.extra count small nonnegative enough] using extra
  refine ⟨nb, after, steps, ?_⟩
  apply readOnly_restore stable (payload_pc (payload_extra (payload_of_repr h.toVmReprAt)
    (s.extra - count.toInt.toNat)) (s.pc + 2)) h.primitives h.running.platform regs
    (loopRegisters_frame (fun r hr => preserved r (by revert r; decide) (by revert r; decide)) h.dispatch.loop)
    post.good (memory.trans dp.memory) (frame.out.trans dp.frame.out)
    (h.geometry.state rfl rfl) h.native (preserved (gprReg 2) (by decide) (by decide))

/-- The satisfied-arity path implements GRAB's corresponding semantic branch. -/
theorem grab_fast_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {count : BitVec 32}
    (stable : MemoryStable L.runtimeOk) (h : ArmInput L P s .GRAB c pl cp sp high)
    (operand : OperandAt P pl (s.pc + 1) count) (nonnegative : 0 ≤ count.toInt)
    (small : s.extra < 2^63) (enough : count.toInt.toNat ≤ s.extra)
    (step : stepI P s ⟨.GRAB, [count.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have state : {s with pc := s.pc + 2, extra := s.extra - count.toInt.toNat} = s' := by
    simpa only [stepI, enough, ite_true, St.adv, Res.next.injEq] using Res.unguard step
  rw [← state]
  exact grab_fast_arm stable h operand nonnegative small enough

end OCaml.Vm.Sim
