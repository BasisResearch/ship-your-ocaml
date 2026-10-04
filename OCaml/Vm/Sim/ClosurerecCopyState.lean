import OCaml.Vm.Sim.CursorCopyState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

def closurerecCopyWrites : List Register := [Register.x13, Register.x14] ++ noiseRegs

abbrev closurerecCopyShape : PointerCopyShape := ⟨true, 23, 14, 11, closurerecCopyWrites⟩

/-- Recursive closures count by destination and recover the source displacement. -/
abbrev ClosurerecCopyRegion := PointerCopyRegion closurerecCopyShape
abbrev ClosurerecCopyAt := PointerCopyAt closurerecCopyShape 0x80002904#64 0x8000291c#64
abbrev ClosurerecCopyPost := PointerCopyPost closurerecCopyShape 0x80002904#64 0x8000291c#64

/-- Subtracting the fixed destination base recovers the source's byte offset. -/
theorem difference_copy_address (source target i : Nat) :
    BitVec.ofNat 64 source + (BitVec.ofNat 64 (target + 8 * i) - BitVec.ofNat 64 target) =
      BitVec.ofNat 64 (source + 8 * i) := by
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 target),
    BitVec.add_sub_cancel, ← BitVec.ofNat_add]

end OCaml.Vm.Sim
