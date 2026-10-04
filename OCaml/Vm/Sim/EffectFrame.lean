import OCaml.Vm.Primitives.Effects
import Vsa.Sim.FrameWriteSet

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Convert the library's indexed write set once for composition with native frames. -/
theorem EffectPost.nativeFrame {writes mem before after pc value}
    (h : EffectPost writes mem before pc value after) :
    StepFrameOut (writes.map gprReg ++ noiseRegs) before.σ after.σ := by
  refine ⟨h.output, ?_⟩
  intro r outside
  apply h.frame r
  · intro n member
    exact beq_eq_false_iff_ne.mp (outside _ (List.mem_append_left _ (List.mem_map.mpr ⟨n, member, rfl⟩)))
  · intro q member
    exact outside q (List.mem_append_right _ member)

end OCaml.Vm.Primitives
