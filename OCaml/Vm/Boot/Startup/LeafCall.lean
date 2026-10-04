import OCaml.Vm.Boot.Startup.PrefixCall
import OCaml.Vm.Primitives.Call
import OCaml.Vm.Primitives.RegisterPins
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A generated direct call to a memory-preserving scalar leaf, retaining
the caller interface across the JAL and the callee return. -/
theorem scalar_leaf_call (call : CallInstr) (shape : CallShape call) (decode : CallDecode call)
    (resultValue : BitVec 64)
    (c : Config) (ra value : BitVec 64) (h : LeafInput ra c) (pins : CallPins call c)
    (parked : GRegs) (holds : GHolds c.σ ((10, value) :: parked))
    (keys : KeysOK (keysG parked)) (avoid : KeysAvoidRa parked)
    (noise : ∀ n ∈ keysG parked, ∀ q ∈ noiseRegs, (q == gprReg n) = false)
    (outside : ∀ n ∈ keysG parked, (gprReg 10 == gprReg n) = false)
    (aligned : call.link.toNat % 4 = 0)
    (callee : ∀ mid, LeafInput call.link mid → FnSummary call.target (fun d => d = mid)
      (WriteRegistersPost [10] [] mid call.link resultValue [(10, resultValue), (1, call.link)])) :
    FnSummary call.pc (fun d => d = c)
      (RegistersPost [1, 10] c.σ.mem c call.link resultValue ((10, resultValue) :: (1, call.link) :: parked)) := by
  have callKeys : KeysOK (keysG ((10, value) :: parked)) := by
    intro n hn
    have choices : n = 10 ∨ n ∈ keysG parked := by simpa only [keysG, List.mem_cons] using hn
    rcases choices with eq | rest
    · subst n; decide
    · exact keys n rest
  have callAvoid : KeysAvoidRa ((10, value) :: parked) := by
    intro n hn
    have choices : n = 10 ∨ n ∈ keysG parked := by simpa only [keysG, List.mem_cons] using hn
    rcases choices with eq | rest
    · subst n; decide
    · exact avoid n rest
  apply summary_bind (pc := call.target) (call_registers_summary shape decode c pins h.good h.image h.tick h.minstret
    _ holds callKeys callAvoid (by rfl)) (fun _ post => post.pc)
  intro mid called
  have leaf : LeafInput call.link mid :=
    ⟨called.good, called.image, called.minstret, called.regs.1, aligned, called.tick⟩
  apply (callee mid leaf).weaken (fun _ eq => eq)
  intro after result
  have kept : GHolds after.σ parked := holds_frame_ne result.frame called.regs.2.2 keys noise (by
    intro n hn m hm
    have eq : m = 10 := List.mem_singleton.mp hm
    subst m
    exact outside n hn)
  have effects := prefix_readonly_post (log := []) called result
  exact ⟨effects.toEffectPost, result.regs.1, result.regs.2.1, kept⟩
end OCaml.Vm.Boot.Startup
