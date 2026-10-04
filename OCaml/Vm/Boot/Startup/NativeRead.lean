import OCaml.Vm.Boot.Startup.NativeFrame
import OCaml.Vm.Primitives.Read
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

def nativeStack (sp : BitVec 64) (size : Nat) : BitVec 64 := sp + (-BitVec.ofNat 64 size)

theorem nativeStack_restore (sp : BitVec 64) (size : Nat) :
    nativeStack sp size + BitVec.ofNat 64 size = sp := by
  rw [nativeStack, ← BitVec.sub_eq_add_neg, BitVec.sub_add_cancel]

theorem NativeFrame.read_slot {sp size} (frame : NativeFrame sp size) {off : Nat}
    (bound : off + 8 ≤ size) (aligned : off % 8 = 0) :
    ReadWindow (nativeStack sp size + BitVec.ofNat 64 off) 8 := by
  rw [nativeStack, frame.address off (by omega)]
  exact (frame.word bound aligned).read

theorem NativeFrame.pins_slot {sp size} (frame : NativeFrame sp size) (c : Config) {off : Nat}
    (bound : off ≤ size) :
    LPins8 c.σ.mem (nativeStack sp size + BitVec.ofNat 64 off).toNat
      (read8 c.σ.mem (nativeFrameBase sp size + off)) := by
  rw [nativeStack, frame.address off bound, frame.slot_nat bound]
  exact read8_pins _ _
end OCaml.Vm.Boot.Startup
