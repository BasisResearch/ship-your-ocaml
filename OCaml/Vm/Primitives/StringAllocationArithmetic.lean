import OCaml.Vm.Primitives.StringAllocation
import VsaIris.Vsa.LibraryAllocFacts
import OCaml.Vm.Repr

namespace OCaml.Vm.Primitives.StringAllocation

/-- Small-string word count, before any allocator side effect. -/
theorem stringWords_toNat (n : Nat) (bound : n < 2^32) :
    (stringWords (BitVec.ofNat 64 n)).toNat = (n + 8) / 8 := by
  simp only [stringWords, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The allocator rounds the payload extent to whole words. -/
theorem stringSpan_toNat (n : Nat) (bound : n < 2^32) :
    (stringSpan (BitVec.ofNat 64 n)).toNat = 8 * ((n + 8) / 8) := by
  unfold stringSpan
  rw [show (-8#64) = BitVec.allOnes 64 <<< (3 : Nat) from rfl]
  rw [VsaIris.MallocFast.and_high_toNat _ 3 (by decide)]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The nursery's string header has the abstract byte-object tag and size. -/
theorem stringHeader_ok (n : Nat) (bound : n < 2^32) :
    HeaderOk ((stringWords (BitVec.ofNat 64 n) <<< 10) + 252#64) ((n + 8) / 8) 252 := by
  unfold HeaderOk
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    stringWords_toNat n bound, BitVec.toNat_ofNat]
  constructor <;> omega

/-- The signed 32-bit padding subtraction is the nonnegative count of
unused payload bytes, even at a word boundary. -/
theorem paddingWord_toNat (n : Nat) (bound : n < 2^32) :
    (paddingWord (stringSpan (BitVec.ofNat 64 n)) (BitVec.ofNat 64 n)).toNat =
      8 * ((n + 8) / 8) - 1 - n := by
  let delta := Sail.BitVec.extractLsb (stringSpan (BitVec.ofNat 64 n) - 1#64) 31 0 -
    Sail.BitVec.extractLsb (BitVec.ofNat 64 n) 31 0
  have count : delta.toNat = 8 * ((n + 8) / 8) - 1 - n := by
    simp only [delta, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
      BitVec.toNat_sub, stringSpan_toNat n bound, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  have positive : delta.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, count]
    omega
  change (delta.signExtend 64).toNat = _
  rw [BitVec.signExtend_eq_setWidth_of_msb_false positive, BitVec.toNat_setWidth, count]
  omega

end OCaml.Vm.Primitives.StringAllocation
