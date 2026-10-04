import OCaml.Vm.Boot.Startup.NativeRead
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem NativeFrame.resize {sp size small} (frame : NativeFrame sp size)
    (bound : small ≤ size) (aligned : small % 16 = 0) : NativeFrame sp small := by
  refine ⟨?_, frame.upper, frame.aligned, aligned⟩
  have lower := frame.lower
  omega

theorem NativeFrame.stack_nat {sp size} (frame : NativeFrame sp size) :
    (nativeStack sp size).toNat = nativeFrameBase sp size := by
  have address := frame.address 0 (Nat.zero_le _)
  change nativeStack sp size + 0#64 = BitVec.ofNat 64 (nativeFrameBase sp size + 0) at address
  rw [BitVec.add_zero, Nat.add_zero] at address
  rw [address]
  exact frame.slot_nat (off := 0) (Nat.zero_le _)

/-- A caller's combined stack bound supplies its callee's nested frame. -/
theorem NativeFrame.nested {sp front size} (frame : NativeFrame sp (front + size))
    (frontAligned : front % 16 = 0) : NativeFrame (nativeStack sp front) size := by
  have first := frame.resize (small := front) (by omega) frontAligned
  have address := first.stack_nat
  have lower := frame.lower
  have upper := frame.upper
  have aligned := frame.aligned
  have totalAligned := frame.sizeAligned
  constructor
  · rw [address]
    unfold nativeFrameBase
    omega
  · rw [address]
    unfold nativeFrameBase
    omega
  · rw [address]
    unfold nativeFrameBase
    omega
  · omega

theorem NativeFrame.nested_base {sp front size} (frame : NativeFrame sp (front + size))
    (frontAligned : front % 16 = 0) :
    nativeFrameBase (nativeStack sp front) size = nativeFrameBase sp (front + size) := by
  have first := frame.resize (small := front) (by omega) frontAligned
  unfold nativeFrameBase
  rw [first.stack_nat]
  unfold nativeFrameBase
  omega
end OCaml.Vm.Boot.Startup
