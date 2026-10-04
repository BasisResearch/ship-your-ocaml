import OCaml.Vm.Sim.ApplyArithmetic

namespace OCaml.Vm.Sim
set_option autoImplicit false

/-- Subtracting payload plus one header word reserves the selected nursery block. -/
theorem nursery_sub_reservation (a count : Nat) (room : 8 ≤ a) (small : count + 1 < 2^61) :
    BitVec.ofNat 64 (a + 8 * count) -
      Sail.shift_bits_left (BitVec.ofNat 64 (count + 1)) (Sail.BitVec.extractLsb (0x03#6) 5 0) =
      BitVec.ofNat 64 (a - 8) := by
  change BitVec.ofNat 64 (a + 8 * count) - (BitVec.ofNat 64 (count + 1) <<< (3 : Nat)) = _
  rw [nat_shift_word, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
  congr 1
  omega

/-- Recursive closures subtract payload bytes and one header via an additive delta. -/
theorem nursery_add_reservation (a count : Nat) (room : 8 ≤ a) (small : count + 1 < 2^61) :
    BitVec.ofNat 64 (a + 8 * count) + (-(8#64) -
      Sail.shift_bits_left (BitVec.ofNat 64 count) (Sail.BitVec.extractLsb (0x03#6) 5 0)) =
      BitVec.ofNat 64 (a - 8) := by
  change BitVec.ofNat 64 (a + 8 * count) + (-(8#64) - (BitVec.ofNat 64 count <<< (3 : Nat))) = _
  rw [nat_shift_word, ← BitVec.neg_add, ← BitVec.sub_eq_add_neg]
  change BitVec.ofNat 64 (a + 8 * count) - (BitVec.ofNat 64 8 + BitVec.ofNat 64 (8 * count)) = _
  rw [← BitVec.ofNat_add, show 8 + 8 * count = 8 * (count + 1) by omega]
  have reserved := nursery_sub_reservation a count room small
  change BitVec.ofNat 64 (a + 8 * count) - (BitVec.ofNat 64 (count + 1) <<< (3 : Nat)) = _ at reserved
  simpa only [nat_shift_word] using reserved

end OCaml.Vm.Sim
