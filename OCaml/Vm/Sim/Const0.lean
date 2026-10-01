import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Sim.Const0Segment
import OCaml.Vm.Sim.Const0Pins

namespace OCaml.Vm.Sim
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Full CONST0 data/platform restoration, by composition of the generated
 dispatch and body. `ArmInput` explicitly records the missing dispatch facts;
 this does not yet discharge the unconditional `ArmSim.next` field. -/
theorem const0_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .CONST0 c pl cp sp high) :
    ∃ c', Plus c c' ∧ Running L P {s with pc := s.pc + 1, accu := .int 0} c' := by
  obtain ⟨nd, d, hnd, hd, dp⟩ := dispatch_run h.dispatch
  have di : ExecutableImage d :=
    ⟨fun i hi => by rw [dp.memory]; exact h.dispatch.image.text i hi,
      fun i hi => by rw [dp.memory]; exact h.dispatch.image.rodata i hi⟩
  have bp : SegSt (0x800035c0#64)
      [⟨Register.x23, BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64⟩]
      (fun σ => Vsa.Sim.Code.CamlConst0Loaded σ.mem ∧ σ.mem = d.σ.mem ∧ σ = d.σ) d :=
    ⟨dp.good, dp.pc, ⟨dp.nextCode, trivial⟩, dp.good.minstret, dp.tick,
      const0_loaded di, rfl, rfl⟩
  obtain ⟨nb, after, hnb, hb, post⟩ := tr_const0 _ d.σ.mem d.σ d bp
  obtain ⟨_, hm, frame⟩ := post.extra
  have memory : after.σ.mem = c.σ.mem := hm.trans dp.memory
  have whole := dp.frame.trans frame
  refine ⟨after, ?_, ?_⟩
  · have hs := hd.append hb
    refine ⟨nd + nb - 1, ?_⟩
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ nd + nb)] using hs
  · apply immediate_restore stable h.toVmReprAt h.running.platform h.dispatch.loop
    refine ⟨post.good, post.pcAt, ?_, ?_, memory, whole.out,
      immediate_preserved whole (by decide)⟩
    · have hp : gpr after Layout.reg_pc = some
          ((BitVec.ofNat 64 (pl.codeBase + 4 * s.pc) + 4#64) + sign_extend (m := 64) (0x000#12)) :=
        PinsHold.get post.pins ⟨1, by simp⟩
      simpa only [show sign_extend (m := 64) (0x000#12) = 0#64 from by decide,
        BitVec.add_zero, codePc_succ] using hp
    · exact PinsHold.get post.pins ⟨0, by simp⟩

end OCaml.Vm.Sim
