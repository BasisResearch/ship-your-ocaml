import OCaml.Vm.Boot.Startup.NativeNested
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim Vsa.Sim.DlHeap OCaml.Vm.Primitives

/-- Four-byte caller output slots share the native stack bounds. -/
theorem NativeFrame.word32 {sp size} (frame : NativeFrame sp size) {off : Nat}
    (bound : off + 4 ≤ size) (aligned : off % 4 = 0) :
    WriteWindow (BitVec.ofNat 64 (nativeFrameBase sp size + off)) 4 := by
  have address := frame.slot_nat (by omega : off ≤ size)
  have lower := frame.lower
  have upper := frame.upper
  have spAligned := frame.aligned
  have sizeAligned := frame.sizeAligned
  constructor <;> rw [address]
  all_goals simp only [nativeFrameBase, heapEnd, Layout.sym_stack_top, Layout.sym_tohost] at *
  all_goals omega

/-- The environment search writes its result index in getenv's outer frame. -/
theorem getenv_offset_window {sp} (frame : NativeFrame sp 32) :
    WriteWindow (nativeStack sp 32 + 12#64) 4 := by
  rw [nativeStack, frame.address 12 (by decide)]
  exact frame.word32 (by decide) (by decide)
end OCaml.Vm.Boot.Startup
