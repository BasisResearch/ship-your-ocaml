import OCaml.Vm.Gc.ForwardedCall
import OCaml.Vm.Gc.ObservationFrame

namespace OCaml.Vm.Gc.ForwardedCall
open Vsa.Machine Vsa.Sim Primitives

/-- The value observations needed by an already-forwarded call are outside
the scan's writes. Layout supplies every runtime field address. -/
structure ObservationsOutside (R : Nat → BitVec 64) (domain : BitVec 64) (ws : List W) : Prop where
  root : OutWRange ws Layout.sym_Caml_state 8
  lower : OutWRange ws (domain + BitVec.ofNat 64 Layout.off_young_start).toNat 8
  upper : OutWRange ws (domain + BitVec.ofNat 64 Layout.off_young_end).toNat 8
  header : OutWRange ws (R 10 - 8#64).toNat 8

/-- Geometric call conditions persist across arbitrary writes in a disjoint
scan/native footprint. Only the four observed words require a memory frame. -/
theorem Conditions.frame {R domain ws before after}
    (conditions : Conditions R domain before)
    (outside : ObservationsOutside R domain ws)
    (frame : FrameOn ws before.σ.mem after.σ.mem) : Conditions R domain after := by
  refine { conditions with root := ?_, lower := ?_, upper := ?_, header := ?_ }
  · exact (frame_word frame outside.root).trans conditions.root
  · change (word after _).toNat < _
    rw [frame_word frame outside.lower]
    exact conditions.lower
  · change _ < (word after _).toNat
    rw [frame_word frame outside.upper]
    exact conditions.upper
  · exact (frame_word frame outside.header).trans conditions.header

end OCaml.Vm.Gc.ForwardedCall
