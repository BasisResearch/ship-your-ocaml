import OCaml.Vm.Primitives.Blocks
import Vsa.Sim.ChainMemory
import Vsa.Sim.Code.Caml_oldify_mopup

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- Every certified collector chain writes above the code image. Reuse this
frame at mopup seams instead of imposing additional code separation. -/
theorem mopupCode_after {bs entry regs loads before after}
    (code : Code.Caml_oldify_mopupLoaded before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) :
    Code.Caml_oldify_mopupLoaded after.σ.mem := by
  apply Code.caml_oldify_mopup_transport code
  intro a _ upper
  rw [post.memory]
  apply evalBlocks_low facts
  have extent : (0x80009f08 : Nat) ≤ tohostAddr := by decide
  omega

end OCaml.Vm.Gc
