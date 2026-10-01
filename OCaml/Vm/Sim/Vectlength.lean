import OCaml.Vm.Sim.SizeRead
import OCaml.Vm.Sim.StackPush
import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.VectlengthSegment
import OCaml.Vm.Sim.VectlengthPins

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- VECTLENGTH reads the selected header and restores its tagged size.
Header geometry and agreement with the abstract size remain explicit. -/
theorem vectlength_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a n : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .VECTLENGTH c pl cp sp high)
    (selected : SizeSelection s pl c a n) (room : 8 ≤ a)
    (read : RamReadAt (a - 8) 8) :
    ∃ c', Plus c c' ∧ Running L P
      {s with pc := s.pc + 1, accu := .int (BitVec.ofNat 63 n)} c' := by
  have source := represented_register h.accu selected.word
  apply immediate_arm stable h
  intro d dp
  obtain ⟨header, headerEq⟩ : ∃ w : BitVec 64, w = word c (a - 8) := ⟨_, rfl⟩
  have loaded : sign_extend (m := 64) (bytesT8 d.σ.mem (a - 8)) = word c (a - 8) := by
    simp only [dp.memory, word, bytesT_eight_eq, sign_extend,
      Sail.BitVec.signExtend, BitVec.signExtend_eq]
  have bp : SegSt (0x8000228c#64)
      [⟨Register.x21, BitVec.ofNat 64 a⟩,
       ⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩]
      (fun σ => Vsa.Sim.Code.CamlVectlengthLoaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc,
      ⟨(dp.frame.frame Register.x21 (by decide)).trans source, dp.nextCode, trivial⟩,
      dp.good.minstret, dp.tick, vectlength_loaded (dp.image h.dispatch.image), rfl, rfl⟩
  have run := tr_vectlength (BitVec.ofNat 64 a)
    (BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) d.σ.mem d.σ
  simp only [push_address room, read.toNat, loaded] at run
  obtain ⟨nb, after, _, hb, post⟩ :=
    run read.lower read.upper read.htif header headerEq d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  refine ⟨nb, after, hb, post.good, post.pcAt, ?_, ?_, hm, frame.out,
    immediate_preserved frame (by decide)⟩
  · have hp : gpr after Layout.reg_pc = some
        ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
      PinsHold.get post.pins ⟨1, by simp⟩
    simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
      BitVec.add_zero, codePc_succ] using hp
  · have hp : gpr after Layout.reg_accu = some
        (((header >>> (10 : Nat)) <<< (1 : Nat)) + 1#64) :=
      PinsHold.get post.pins ⟨0, by simp⟩
    have size : header.toNat / 1024 = n := by rw [headerEq]; exact selected.header
    simpa only [header_size_tag header n size] using hp

/-- Connect the selected size to the actual successful bytecode rule. -/
theorem vectlength_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a n : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .VECTLENGTH c pl cp sp high)
    (selected : SizeSelection s pl c a n) (room : 8 ≤ a)
    (read : RamReadAt (a - 8) 8)
    (step : stepI P s ⟨.VECTLENGTH, []⟩ = .next s') :
    ∃ c', Plus c c' ∧ Running L P s' c' := by
  have state : {s with pc := s.pc + 1, accu := .int (BitVec.ofNat 63 n)} = s' := by
    simpa [stepI, selected.size, opt, St.adv, Val.ofInt] using step
  rw [← state]
  exact vectlength_arm stable h selected room read

end OCaml.Vm.Sim
