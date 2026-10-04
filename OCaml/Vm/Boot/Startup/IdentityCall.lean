import OCaml.Vm.Boot.Startup.Identity
import OCaml.Vm.Primitives.Call
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- A generated direct call to any identity function, retaining a caller's
finite interface across both the JAL and the callee's zero return. -/
theorem identity_call (kind : IdentityKind) (call : CallInstr)
    (shape : CallShape call) (decode : CallDecode call) (target : call.target = kind.entry)
    (c : Config) (ra value : BitVec 64) (h : LeafInput ra c) (pins : CallPins call c)
    (parked : GRegs) (holds : GHolds c.σ ((10, value) :: parked))
    (keys : KeysOK (keysG parked)) (avoid : KeysAvoidRa parked)
    (noise : ∀ n ∈ keysG parked, ∀ q ∈ noiseRegs, (q == gprReg n) = false)
    (outside : ∀ n ∈ keysG parked, (gprReg 10 == gprReg n) = false)
    (aligned : call.link.toNat % 4 = 0) :
    FnSummary call.pc (fun d => d = c)
      (RegistersPost [1, 10] c.σ.mem c call.link 0#64 ((10, 0#64) :: (1, call.link) :: parked)) := by
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
  apply summary_bind (pc := kind.entry) (call_registers_summary shape decode c pins h.good h.image h.tick h.minstret
    _ holds callKeys callAvoid (by rfl)) (fun _ post => by rw [← target]; exact post.pc)
  intro mid called
  have leaf : LeafInput call.link mid :=
    ⟨called.good, called.image, called.minstret, called.regs.1, aligned, called.tick⟩
  apply (identity_zero kind mid _ leaf).weaken (fun _ eq => eq)
  intro after result
  have kept : GHolds after.σ parked := holds_frame_ne result.frame called.regs.2.2 keys noise (by
    intro n hn m hm
    have eq : m = 10 := List.mem_singleton.mp hm
    subst m
    exact outside n hn)
  have effects := called.toEffectPost.trans result.toEffectPost
  exact ⟨⟨effects.good, effects.image, effects.minstret, effects.tick, effects.pc, effects.result,
    result.memory.trans called.memory, effects.output, effects.frame⟩,
    result.regs.1, result.regs.2.1, kept⟩
end OCaml.Vm.Boot.Startup
