import OCaml.Vm.Boot.Startup.AllocatorInitial
import VsaIris.Vsa.Instance
namespace OCaml.Vm.Boot.WhileMinElfParse
open Vsa.Machine Vsa.Sim Startup LeanRV64DExecutable

/-- Every source-initialized GPR is still present at the runtime entry. -/
theorem ResetCamlMainWitness.gprs {initial after : Config} (w : ResetCamlMainWitness initial after) :
    GprPresent after.σ := by
  apply w.post.gprs
  constructor
  intro n lo hi
  change (gprGet initial.σ n).isSome
  rw [w.reset.gprs n lo hi]
  rfl

theorem ResetCamlMainWitness.idle {initial after : Config} (w : ResetCamlMainWitness initial after) :
    after.σ.regs.get? .htif_payload_writes = some 0#4 :=
  (w.post.frame .htif_payload_writes (by decide) (by decide)).trans w.reset.idle

theorem ResetDomainWitness.gprs {initial atMain atDomain : Config}
    (w : ResetDomainWitness initial atMain atDomain) : GprPresent atDomain.σ :=
  w.main.gprs.of_regs_ne (writes := [2, 9, 1]) (by decide) w.post.regs
    (by simp only [keysG]; decide) w.post.frame

theorem ResetDomainWitness.idle {initial atMain atDomain : Config}
    (w : ResetDomainWitness initial atMain atDomain) :
    atDomain.σ.regs.get? .htif_payload_writes = some 0#4 :=
  (w.post.frame .htif_payload_writes (by decide) (by decide)).trans w.main.idle

theorem ResetStatAllocWitness.gprs {initial atMain atDomain atAlloc : Config}
    (w : ResetStatAllocWitness initial atMain atDomain atAlloc) : GprPresent atAlloc.σ :=
  w.domain.gprs.of_regs_ne (writes := [15, 2, 10, 1]) (by decide) w.post.regs
    (by simp only [keysG]; decide) w.post.frame

theorem ResetStatAllocWitness.idle {initial atMain atDomain atAlloc : Config}
    (w : ResetStatAllocWitness initial atMain atDomain atAlloc) :
    atAlloc.σ.regs.get? .htif_payload_writes = some 0#4 :=
  (w.post.frame .htif_payload_writes (by decide) (by decide)).trans w.domain.idle

/-- Complete architectural register presence at the actual first malloc call. -/
theorem ResetMallocWitness.gprs {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) : GprPresent atMalloc.σ :=
  w.alloc.gprs.of_regs_ne (writes := [15]) (by decide) w.post.regs
    (by simp only [keysG]; decide) w.post.frame

theorem ResetMallocWitness.idle {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) :
    atMalloc.σ.regs.get? .htif_payload_writes = some 0#4 :=
  (w.post.frame .htif_payload_writes (by decide) (by decide)).trans w.alloc.idle

/-- Any live image footprint inside RAM has the library model's full platform
invariant at the actual reset-reachable first malloc entry. -/
theorem ResetMallocWitness.vsaOk {initial atMain atDomain atAlloc atMalloc : Config}
    (w : ResetMallocWitness initial atMain atDomain atAlloc atMalloc) (live : Nat → Prop)
    (inRam : ∀ a, live a → Vsa.Densify.ramBase ≤ a ∧ a < Vsa.Densify.ramBase + Vsa.Densify.ramSize) :
    VsaIris.Inst.VsaOk live atMalloc where
  good := w.post.good
  tick := w.post.tick
  gpr := fun n lo hi => w.gprs.get n lo (by omega)
  live := fun a ha => w.present a (inRam a ha).1 (inRam a ha).2
  htifIdle := w.idle
end OCaml.Vm.Boot.WhileMinElfParse
