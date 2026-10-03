import OCaml.Vm.Gc.Readback
import OCaml.Vm.Reloc

namespace OCaml.Vm.Gc
open Vsa.Machine Vsa.Sim Primitives

/-- A disjoint scalar range is pointwise outside every permitted window. -/
theorem outW_of_range {ws : List W} {a n j : Nat}
    (outside : OutWRange ws a n) (bound : j < n) : OutW ws (a + j) := by
  induction ws with
  | nil => trivial
  | cons w ws ih => exact ⟨by have := outside.1; omega, ih outside.2⟩

/-- Arbitrary permitted write windows preserve a separate word observation. -/
theorem frame_word {ws : List W} {before after : Config} {a : Nat}
    (frame : FrameOn ws before.σ.mem after.σ.mem)
    (outside : OutWRange ws a 8) : word after a = word before a := by
  apply Reloc.bytesT_congr
  intro j bound
  change byte after (a + j) = byte before (a + j)
  rw [byte_total, byte_total, frame (a + j) (outW_of_range outside bound)]

end OCaml.Vm.Gc
