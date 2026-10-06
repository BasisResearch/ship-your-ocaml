import OCaml.Vm.Sim.BinaryLibInput
import OCaml.Vm.Sim.Muldi3Pins
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.Muldi3Any

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- Multiplication's library entry: operands and return address only. The
scratch registers need not be present (`muldi3_spec_any`: `__muldi3` writes
`a2`/`a3` before reading them). -/
structure Muldi3Input (x y ra : BitVec 64) (c : Config) : Prop extends LeafInput ra c where
  left : gpr c 10 = some x
  right : gpr c 11 = some y

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
  have pre : muldi3_pre_any c.σ.regs.get? x y ra c.σ.mem c.σ.sailOutput c :=
    ⟨⟨none, none, input.good, muldi3_loaded input.image, rfl, rfl, pc,
      input.left, input.right, nofun, nofun, input.raReg, input.minstret,
      input.tick, fun _ _ => rfl⟩, input.aligned⟩
  obtain ⟨after, run, post⟩ := muldi3_spec_any _ x y ra _ _ c pre
  exact ⟨after, run, muldi3_post_named input post⟩

end OCaml.Vm.Sim
