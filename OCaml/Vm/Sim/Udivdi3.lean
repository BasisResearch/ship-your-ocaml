import OCaml.Vm.Sim.BinaryLibInput
import OCaml.Vm.Sim.Udivdi3Pins
import Vsa.Sim.DivLoops
import Vsa.Sim.DivAny

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- Unsigned division needs its operands, a nonzero divisor and a return
address; the scratch registers need not be present (`udivdi3_spec_any`). -/
structure Udivdi3Input (x y ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  left : gpr c 10 = some x
  right : gpr c 11 = some y
  nonzero : y ≠ 0

/-- The existing division core returns quotient and remainder together. -/
structure Udivdi3Post (before : Config) (ra quotient remainder : BitVec 64) (after : Config) : Prop
    extends LeafInput ra after where
  pc : pcOf after = some ra
  quotientReg : gpr after 10 = some quotient
  remainderReg : gpr after 11 = some remainder
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r, NotWritten r → after.σ.regs.get? r = before.σ.regs.get? r
  scratch2 : ∃ v, gpr after 12 = some v
  scratch3 : ∃ v, gpr after 13 = some v

/-- Destructure the upstream result once at the named library boundary. -/
theorem udivdi3_post_named {before after : Config} {x y ra : BitVec 64}
    (input : Udivdi3Input x y ra before)
    (post : udivdi3_post before.σ.regs.get? x y ra before.σ.mem before.σ.sailOutput after) :
    Udivdi3Post before ra (x / y) (x % y) after := by
  obtain ⟨good, memory, output, pc, quotient, remainder, ret, tick, frame, scratch2, scratch3⟩ := post
  have image : ExecutableImage after :=
    ⟨by simpa only [memory] using input.image.text,
     by simpa only [memory] using input.image.rodata⟩
  exact ⟨⟨good, image, good.minstret, ret, input.aligned, tick⟩,
    pc, quotient, remainder, memory, output, frame, scratch2, scratch3⟩

/-- Reuse the proved total unsigned division core, including its remainder
and complete register frame, for both signed wrappers. -/
theorem udivdi3_summary {before : Config} {x y ra : BitVec 64}
    (input : Udivdi3Input x y ra before) :
    FnSummary 0x800372a0#64 (fun c => c = before) (Udivdi3Post before ra (x / y) (x % y)) := by
  constructor
  rintro c ⟨pc, rfl⟩
  have divisor : 0 < y.toNat := by
    have nonzero := input.nonzero
    have positive : y.toNat ≠ 0 := by
      intro zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact zero
    omega
  have pre : udivdi3_pre_any c.σ.regs.get? x y ra c.σ.mem c.σ.sailOutput c :=
    ⟨⟨none, none, input.good, udivdi3_loaded input.image, rfl, rfl, pc,
      input.left, input.right, nofun, nofun, input.raReg, input.minstret,
      input.tick, fun _ _ => rfl⟩, divisor, input.aligned⟩
  obtain ⟨after, run, post⟩ := udivdi3_spec_any _ x y ra _ _ c pre
  exact ⟨after, run, udivdi3_post_named input post⟩

end OCaml.Vm.Sim
