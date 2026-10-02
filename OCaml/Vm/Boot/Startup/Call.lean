import Vsa.Sim.BridgeSeg
import Vsa.Sim.FnSummary

/-! Named call-seam observations, supplied only by generated JAL sites. -/
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions

structure CallPost (target link : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  memory : after.σ.mem = before.σ.mem
  pc : PCAt target after
  linkReg : gprGet after.σ 1 = some link
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    r ≠ .x1 → after.σ.regs.get? r = before.σ.regs.get? r

theorem CallPost.of_obs {before after : Config} {pc vm target link : BitVec 64} {imm : BitVec 21}
    (good : GoodState after.σ) (tick : after.tick < 2)
    (memory : after.σ.mem = before.σ.mem)
    (obs : ReadsLikePost after.σ (sigmaPost_jal before.σ pc vm imm .x1 link))
    (address : pc + sign_extend (m := 64) imm = target) : CallPost target link before after := by
  refine ⟨good, tick, memory, ?_, ?_, obs.out, ?_⟩
  · rw [← address]; exact obs_jal_pc obs
  · exact obs_jal_rd obs (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro r hn hr
    have noise (x : Register) (hx : x ∈ noiseRegs) := hn x hx
    rw [obs.1 r (noise _ (by simp [noiseRegs])) (noise _ (by simp [noiseRegs]))
      (noise _ (by simp [noiseRegs]))]
    exact get?_sigmaPost_jal _ _ _ _ _ _ r
      (noise _ (by simp [noiseRegs])) (noise _ (by simp [noiseRegs]))
      (by simpa only [beq_eq_false_iff_ne] using Ne.symm hr)
      (noise _ (by simp [noiseRegs])) (noise _ (by simp [noiseRegs]))

end OCaml.Vm.Boot.Startup
