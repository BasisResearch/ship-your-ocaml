import OCaml.Vm.Boot.Startup.Identity
import OCaml.Vm.Boot.Startup.LeafCall
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
  apply scalar_leaf_call call shape decode 0#64 c ra value h pins parked holds keys avoid noise outside aligned
  intro mid leaf
  rw [target]
  exact identity_zero kind mid _ leaf
end OCaml.Vm.Boot.Startup
