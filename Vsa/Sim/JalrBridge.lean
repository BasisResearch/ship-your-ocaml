import Vsa.Sim.JalrFrame
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.GRegsFrame

namespace Vsa.Sim
open Vsa.Machine LeanRV64DExecutable Sail

/-- An indirect linking jump supplies the same call-boundary interface as
an observed direct JAL. The shared register frame avoids a per-site GPR proof. -/
theorem jalrCallFacts_of_obs {σ σ' : MState} {i u i' : Nat} {pc vm target link : BitVec 64}
    (step : Step ⟨σ,i,u⟩ ⟨σ',i',u+1⟩) (tick : i' < 2) (good : GoodState σ')
    (memory : σ'.mem = σ.mem)
    (obs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm target Register.x1 link)) :
    JalCallFacts target link ⟨σ,i,u⟩ ⟨σ',i',u+1⟩ := by
  have framed := StepFrameOut.of_jalr obs
  refine ⟨step, good, tick, obs_jalr_pc obs,
    obs_jalr_rd obs (by decide) (by decide) (by decide) (by decide) (by decide),
    obs_jalr_minstret obs, memory, ?_, framed⟩
  intro n low high notRa value pin
  have noise : ∀ n, n < 32 → ∀ r ∈ noiseRegs, (r == gprReg n) = false := by decide
  have ra : (gprReg 1 == gprReg n) = false :=
    gprReg_beq_false 1 (by decide) n (by omega) (by decide) low (Ne.symm notRa)
  apply (gprGet_of_frame (wrs := [1]) n low high (noise n (by omega)) ?_ ?_).trans pin
  · intro m member
    have same : m = 1 := List.mem_singleton.mp member
    simpa only [same] using ra
  · intro r silent untouched
    apply framed.frame
    intro q member
    rcases List.mem_cons.mp member with rfl | member
    · exact untouched 1 (by simp)
    · exact silent q member

end Vsa.Sim
