import OCaml.Vm.Sim.BinaryLibInput
import OCaml.Vm.Sim.Muldi3Pins
import Vsa.Sim.Muldi3Spec

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Multiplication uses the shared binary-library register interface. -/
abbrev Muldi3Input := BinaryLibInput

/-- Named return view of the landed libgcc contract, with its complete frame. -/
structure Muldi3Post (before : Config) (ra value : BitVec 64) (after : Config) : Prop
    extends LeafInput ra after where
  pc : pcOf after = some ra
  result : gpr after 10 = some value
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ r, NotWrittenM r → after.σ.regs.get? r = before.σ.regs.get? r

/-- Destructure the upstream conjunction once, at the named library boundary. -/
theorem muldi3_post_named {before after : Config} {x y ra : BitVec 64}
    (input : Muldi3Input x y ra before)
    (post : muldi3_post before.σ.regs.get? x y ra before.σ.mem before.σ.sailOutput after) :
    Muldi3Post before ra (x * y) after := by
  obtain ⟨good, memory, output, pc, result, ret, tick, frame⟩ := post
  have image : ExecutableImage after :=
    ⟨by simpa only [memory] using input.image.text,
     by simpa only [memory] using input.image.rodata⟩
  exact ⟨⟨good, image, good.minstret, ret, input.aligned, tick⟩,
    pc, result, memory, output, frame⟩

/-- The existing total libgcc multiply proof as a reusable machine summary. -/
theorem muldi3_summary {before : Config} {x y ra : BitVec 64}
    (input : Muldi3Input x y ra before) :
    FnSummary 0x80037234#64 (fun c => c = before) (Muldi3Post before ra (x * y)) := by
  constructor
  rintro c ⟨pc, rfl⟩
  obtain ⟨v2, h2⟩ := input.scratch2
  obtain ⟨v3, h3⟩ := input.scratch3
  have pre : muldi3_pre c.σ.regs.get? x y ra c.σ.mem c.σ.sailOutput c :=
    ⟨⟨v2, v3, input.good, muldi3_loaded input.image, rfl, rfl, pc,
      input.left, input.right, h2, h3, input.raReg, input.minstret,
      input.tick, fun _ _ => rfl⟩, input.aligned⟩
  obtain ⟨after, run, post⟩ := muldi3_spec _ x y ra _ _ c pre
  exact ⟨after, run, muldi3_post_named input post⟩

end OCaml.Vm.Sim
