import Vsa.Sim.StepFrameOut
import Vsa.Sim.LibraryJalrFacts

/-! Indirect linking jumps use the same frame and pin composition as direct calls. -/
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)

namespace Vsa.Sim

/-- An indirect call writes its link register and the ordinary step/tick noise. -/
theorem StepFrameOut.of_jalr {σ σ' : MState} {pc vm tgt : BitVec 64}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd link)) :
    StepFrameOut (rd :: noiseRegs) σ σ' where
  out := hobs.out
  frame := by
    intro R hR
    have noise (r : Register) (hr : r ∈ noiseRegs) : (r == R) = false :=
      hR r (List.mem_cons_of_mem rd hr)
    exact (hobs.1 R (noise _ (by decide)) (noise _ (by decide))
      (noise _ (by decide))).trans
      (post_jalr_other σ pc vm tgt rd link R
        (noise _ (by decide)) (noise _ (by decide))
        (hR _ (List.mem_cons_self ..)) (noise _ (by decide)) (noise _ (by decide)))

/-- Preserve an entire pin bundle through an indirect call instruction. -/
theorem pins_jalr {σ' σ : MState} {pc vm tgt : BitVec 64}
    {rd : Register} {link : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_jalr σ pc vm tgt rd link)) {L : List Pin}
    (hav : pinsAvoid (rd :: noiseRegs) L = true)
    (h : PinsHold σ L) : PinsHold σ' L :=
  pins_of_frame (StepFrameOut.of_jalr hobs).frame hav h

end Vsa.Sim
