import OCaml.Vm.Gc.BfShape
import OCaml.Vm.Boot.WhileMinRuntimeReads

/-! Bounded bitmap production from existing startup observations. The captured
memory certificate is a memory witness, not a native reset execution. -/
namespace OCaml.Vm.Gc.BfShape
open Vsa.Machine Vsa.Sim Primitives

/-- The repository's singleton startup predicate includes an actual zero map. -/
theorem bounded_of_singleton {c b} (startup : Boot.BestFitSingletonAt c b) :
    BoundedBitmap c.σ.mem := BoundedBitmap.of_zero startup.bitmap

/-- Empty lists and the zero map observed by the startup shape supply the
bounded representation. Native execution/caller production remains separate. -/
theorem boundedSmall_of_singleton {c b} (startup : Boot.BestFitSingletonAt c b) :
    BoundedSmallRepresentation c.σ.mem (fun _ => []) := by
  refine ⟨⟨⟨?_,?_,?_⟩,⟨?_⟩,?_,SmallPhysical.empty⟩,bounded_of_singleton startup⟩
  · intro s lo hi
    change bytesT c.σ.mem (slot s).toNat 8 = 0#64
    rw [slot_toNat s hi]
    simpa [word,Boot.smallSlot,Layout.off_bf_small_free,Layout.bf_small_size,Nat.mul_comm] using (startup.small s lo hi).head
  · intro s lo hi x hx
    simp at hx
  · intro s lo hi x hx
    simp at hx
  · intro s lo hi x hx
    simp at hx
  · intro s lo hi
    change (mapBits c.σ.mem).getLsbD (s-1) = true ↔ _
    rw [show mapBits c.σ.mem = 0#32 from startup.bitmap]
    simp

/-- Exact scope of the available captured-memory producer: any memory
zero-equivalent to the checked observed log has a bounded bitmap. -/
theorem bounded_of_observed {c : Config} {initial : Vsa.MemRepr.Mem}
    (memory : Vsa.Densify.MemEqv c.σ.mem
      (Vsa.Sim.Boot.observedMem initial Boot.WhileMinLog.log)) : BoundedBitmap c.σ.mem :=
  BoundedBitmap.of_zero (Boot.WhileMinRuntime.read_bf_small_map memory)
end OCaml.Vm.Gc.BfShape
