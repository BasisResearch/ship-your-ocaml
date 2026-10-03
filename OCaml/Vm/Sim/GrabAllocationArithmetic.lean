import OCaml.Vm.Sim.GrabArithmetic
import OCaml.Vm.Sim.StackPush

namespace OCaml.Vm.Sim
set_option autoImplicit false
open LeanRV64DExecutable.Functions

/-- Insufficient arity takes the allocating GRAB branch under signed bounds. -/
theorem grab_alloc_guard (extra : Nat) (required : BitVec 32)
    (small : extra < 2^63) (nonnegative : 0 ≤ required.toInt) (short : extra < required.toInt.toNat) :
    zopz0zI_s (BitVec.ofNat 64 extra) (sign_extend (m := 64) required) = true := by
  rw [nonnegative_word32 required nonnegative]
  unfold zopz0zI_s
  rw [nat64_toInt extra small, nat64_toInt required.toInt.toNat (by have bound := BitVec.toInt_lt (x := required); omega)]
  exact decide_eq_true (by omega)

/-- GRAB allocates its saved arguments plus three metadata fields. -/
theorem grab_size_word (extra : Nat) :
    BitVec.ofNat 64 extra + sign_extend (m := 64) (0x004#12) = BitVec.ofNat 64 (extra + 4) := by
  rw [show sign_extend (m := 64) (0x004#12) = BitVec.ofNat 64 4 from by decide, ← BitVec.ofNat_add]

/-- Reserving payload plus header produces the selected nursery header address. -/
theorem grab_reservation_word (a count : Nat) (room : 8 ≤ a) :
    BitVec.ofNat 64 (a + 8 * count) +
      (((0#64) + sign_extend (m := 64) (0xff8#12)) -
        Sail.shift_bits_left (BitVec.ofNat 64 count) (Sail.BitVec.extractLsb (0x03#6) 5 0)) =
      BitVec.ofNat 64 (a - 8) := by
  change BitVec.ofNat 64 (a + 8 * count) + ((0#64 + sign_extend (m := 64) (0xff8#12)) -
    (BitVec.ofNat 64 count <<< (3 : Nat))) = _
  rw [nat_shift_word, BitVec.ofNat_add]
  have address := push_address room
  rw [← address]
  bv_omega

end OCaml.Vm.Sim
