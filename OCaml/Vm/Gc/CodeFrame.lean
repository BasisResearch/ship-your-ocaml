import OCaml.Vm.Primitives.Blocks
import Vsa.Sim.ChainMemory
import Vsa.Sim.Code.Caml_oldify_mopup
import Vsa.Sim.Code.Caml_oldify_one

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- A certified scalar-store chain preserves any image wholly below the
store policy's lower bound. Generated image transports instantiate this once. -/
theorem image_after {bs entry regs loads before after lo hi}
    {Image : Std.ExtHashMap Nat (BitVec 8) → Prop}
    (transport : ∀ {m m'}, Image m →
      (∀ a, lo ≤ a → a < hi → m'[a]? = m[a]?) → Image m')
    (bound : hi ≤ tohostAddr) (code : Image before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) : Image after.σ.mem := by
  apply transport code
  intro a _ upper
  rw [post.memory]
  apply evalBlocks_low facts
  omega

/-- Collector code survives the chain's permitted stores. -/
theorem mopupCode_after {bs entry regs loads before after}
    (code : Code.Caml_oldify_mopupLoaded before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) :
    Code.Caml_oldify_mopupLoaded after.σ.mem :=
  image_after Code.caml_oldify_mopup_transport (by decide) code facts post

/-- Oldify code survives the same scalar-store policy. -/
theorem oldifyCode_after {bs entry regs loads before after}
    (code : Code.Caml_oldify_oneLoaded before.σ.mem)
    (facts : ChainFacts before.σ.mem before.σ.mem regs loads bs)
    (post : BlockPost bs entry regs loads before after) :
    Code.Caml_oldify_oneLoaded after.σ.mem :=
  image_after Code.caml_oldify_one_transport (by decide) code facts post

end OCaml.Vm.Gc
